/* Based on nullgrind */
#include <sys/types.h>
#include <errno.h>
#include <stdlib.h>

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_options.h"

#include "libvex_guest_offsets.h"

#include "dumpfile.h"

static const char *tag_table;

/* A couple of experiments on inkscape:

   ~20% of memory in some goes on allocations of less than 50 bytes.
   ~50% goes on allocations of less then ~500 bytes.
   ~90% goes on allocations of less than 12k.

   In one trivial test we used 52MiB in total across 420k allocations,
   for a mean allocation size of a bit over 100 bytes.
*/

/* Big hash table from addresses to (allocation_rip, allocation_size)
   pairs.  Could be more clever than this and take advantage of
   contiguity properties (e.g. using a splay tree), but I really can't
   be bothered.  Each entry covers an eight-byte region, and the
   offset in the tag gives the *start* of that region. */
struct address_hash_entry {
	struct address_hash_entry *next;
	unsigned long addr;
	int is_private; /* This location is believed to be (roughly)
			 * private heap. */
	struct type_tag tag;
};

#define ADDR_REGION_SIZE 8
#define NR_ADDR_HASH_ENTRIES 8193
static struct address_hash_entry *
address_hash_heads[NR_ADDR_HASH_ENTRIES];

/* And another one mapping from the addresses of store instructions to
   the tags which they store to.  If we discover that one RIP seems to
   be storing to an enormous number of tags then we start considering
   its caller as well, in which case the bad RIP gets left in the
   table with a flag saying that you need to look at its parent.  It
   happens that the return addresses provided by the Valgrind stack
   walker pointinto the middle of the call instructions, which is a
   bit weird but very convenient, as we know that there can never be a
   store with the same address, which makes some things a bit more
   convenient.
*/
#define MAX_RANGES_PER_STORE 8
struct store_hash_entry {
	struct store_hash_entry *next;
	unsigned long rip;
	struct range range1; /* The common case is that each store
				writes precisely one range, so keep
				one inline. */
	int nr_ranges; /* This is zero if we should backtrack another
			level up the call stack. */
	struct range *out_of_line_ranges;
};
#define NR_STORE_HASH_HEADS 4097
static struct store_hash_entry *
store_hash_heads[NR_STORE_HASH_HEADS];

struct thread_extra_data {
	struct thread_extra_data *next;
	ThreadId tid;
	unsigned nr_stack_slots;
	unsigned nr_stack_slots_allocated;
	unsigned long *stack;
};

#define NR_THREAD_EXTRA_HEADS 32
static struct thread_extra_data *
thread_extra_heads[NR_THREAD_EXTRA_HEADS];

static void
build_tag(struct type_tag *t, ThreadId tid, SizeT sz, int is_realloc)
{
	Addr stack[2];
	int n;

	t->offset = 0;
	if (is_realloc)
		t->allocation_size = -sz;
	else
		t->allocation_size = sz;
	n = VG_(get_StackTrace)(tid, stack, 2, NULL, NULL, 0);
	tl_assert(n == 2);
	t->allocation_rip = stack[1];
}

static unsigned long
hash_ptr(const void *_ptr)
{
	unsigned long ptr = (unsigned long)_ptr;
	tl_assert(!(ptr % ADDR_REGION_SIZE));
	ptr /= ADDR_REGION_SIZE;
	while (ptr >= NR_ADDR_HASH_ENTRIES)
		ptr = (ptr / NR_ADDR_HASH_ENTRIES) ^ (ptr % NR_ADDR_HASH_ENTRIES);
	return ptr;
}

static unsigned long
hash_store_addr(unsigned long rip)
{
	unsigned long hash = rip;
	while (hash >= NR_STORE_HASH_HEADS)
		hash = (hash / NR_STORE_HASH_HEADS) ^ (hash % NR_STORE_HASH_HEADS);
	return hash;
}

static struct address_hash_entry *
find_address_hash_entry(unsigned long addr)
{
	struct address_hash_entry *e;
	addr -= addr % ADDR_REGION_SIZE;
	for (e = address_hash_heads[hash_ptr((void *)addr)];
	     e && e->addr != addr;
	     e = e->next)
		;
	return e;
}

static void
clear_allocation_tag(void *p)
{
	struct address_hash_entry **pprev, *e;
	unsigned long h = hash_ptr(p);
	SizeT sz;
	int x;

	pprev = &address_hash_heads[h];
	e = *pprev;
	while (e && e->addr != (unsigned long)p) {
		pprev = &e->next;
		e = *pprev;
	}
	tl_assert(e);
	sz = labs(e->tag.allocation_size);
	*pprev = e->next;
	VG_(free)(e);
	for (x = 16; x < sz; x += ADDR_REGION_SIZE) {
		h = hash_ptr((void *)((unsigned long)p + x));
		pprev = &address_hash_heads[h];
		e = *pprev;
		while (e && e->addr != (unsigned long)p + x) {
			pprev = &e->next;
			e = *pprev;
		}
		tl_assert(e);
		tl_assert(labs(e->tag.allocation_size) == sz);
		*pprev = e->next;
		VG_(free)(e);
	}
}

static void
register_allocation(void *ptr, SizeT sz, ThreadId tid, int is_realloc)
{
	int x;
	struct address_hash_entry *e;
	struct type_tag tag;
	unsigned long h;

	build_tag(&tag, tid, sz, is_realloc);

	for (x = 0; x < sz; x += ADDR_REGION_SIZE) {
		e = VG_(malloc)("address_hash_entry", sizeof(*e));
		e->addr = (unsigned long)ptr + x;
		e->tag = tag;
		e->is_private = 1;
		e->tag.offset = x;
		h = hash_ptr((void *)e->addr);
		e->next = address_hash_heads[h];
		address_hash_heads[h] = e;
	}
}

struct read_file {
	int fd;
	unsigned buf_cons;
	unsigned buf_prod;
	unsigned char buf[128];
};

static int
open_read_file(struct read_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(tag_table, VKI_O_RDONLY, 0);
	if (sr.isError)
		return sr.err;
	out->fd = sr.res;
	out->buf_cons = 0;
	out->buf_prod = 0;
	return 0;
}

static int
read_file(struct read_file *rf, void *buf, size_t sz)
{
	unsigned to_copy;
	Int x;

	if (sz == 0)
		return 1;
	while (1) {
		to_copy = sz;
		if (rf->buf_prod > rf->buf_cons) {
			if (rf->buf_prod - rf->buf_cons < sz)
				to_copy = rf->buf_prod - rf->buf_cons;
			VG_(memcpy)(buf, rf->buf + rf->buf_cons, to_copy);
			rf->buf_cons += to_copy;
			sz -= to_copy;
			buf = (void *)((unsigned long)buf + to_copy);
			if (!sz)
				return 1;
		}
		tl_assert(rf->buf_prod == rf->buf_cons);
		rf->buf_cons = rf->buf_prod = 0;
		x = VG_(read)(rf->fd, rf->buf + rf->buf_prod, sizeof(rf->buf) - rf->buf_prod);
		if (x == 0)
			return 0;
		tl_assert(x > 0);
		rf->buf_prod += x;
	}
}

static void
close_read_file(struct read_file *rf)
{
	VG_(close)(rf->fd);
}

static void
ft_post_clo_init(void)
{
	int err;
	struct read_file rf;
	struct table_site_header tsh;
	struct store_hash_entry *e;
	unsigned long hash;

	VG_(clo_vex_control).guest_chase_thresh = 0;

	err = open_read_file(&rf, tag_table);
	if (err) {
		if (err == ENOENT) {
			/* Just use an empty table */
			return;
		}
		VG_(tool_panic)("failed to open tag table");
	}
	while (1) {
		if (!read_file(&rf, &tsh, sizeof(tsh)))
			break; /* Assume we hit end-of-file */
		e = VG_(malloc)("store_hash_entry", sizeof(*e));
		e->rip = tsh.rip;
		e->nr_ranges = tsh.nr_ranges;
		if (e->nr_ranges != 0)
			read_file(&rf, &e->range1, sizeof(e->range1));
		if (e->nr_ranges > 1) {
			e->out_of_line_ranges =
				VG_(malloc)("out of line range table",
					    sizeof(e->out_of_line_ranges[0]) * (e->nr_ranges - 1));
			read_file(&rf, e->out_of_line_ranges,
				  sizeof(e->out_of_line_ranges[0]) * (e->nr_ranges - 1));
		}
		hash = hash_store_addr(e->rip);
		e->next = store_hash_heads[hash];
		store_hash_heads[hash] = e;
	}
	close_read_file(&rf);
}

static IRTemp
cast_to_U64(IRSB *irsb, IRExpr *expr)
{
	IROp op;
	IRTemp tmp;

	switch (typeOfIRExpr(irsb->tyenv, expr)) {
	case Ity_I8:
		op = Iop_8Uto64;
		break;
	case Ity_I16:
		op = Iop_16Uto64;
		break;
	case Ity_I32:
		op = Iop_32Uto64;
		break;
	case Ity_F64:
		op = Iop_ReinterpF64asI64;
		break;
	case Ity_F32:
		tmp = newIRTemp(irsb->tyenv, Ity_I32);
		addStmtToIRSB(irsb,
			      IRStmt_WrTmp(tmp,
					   IRExpr_Unop(Iop_ReinterpF32asI32,
						       expr)));
		return cast_to_U64(irsb,
				   IRExpr_RdTmp(tmp));
	default:
		VG_(tool_panic)((Char *)"Weird-arse type problem.\n");
	}
	tmp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(tmp,
				   IRExpr_Unop(op, expr)));
	return tmp;
}

static void
add_dirty_call(IRSB *irsb,
	       char *name,
	       void *ptr,
	       ...)
{
	va_list args;
	int nr_args;
	IRExpr *e;
	IRExpr **arg_v;
	IRDirty *dirty;

	va_start(args, ptr);
	nr_args = 0;
	while (1) {
		e = va_arg(args, IRExpr *);
		if (!e)
			break;
		nr_args++;
	}
	va_end(args);

	arg_v = LibVEX_Alloc( (nr_args + 1) * sizeof(arg_v[0]) );
	va_start(args, ptr);
	nr_args = 0;
	while (1) {
		e = va_arg(args, IRExpr *);
		if (!e)
			break;
		arg_v[nr_args] = e;
		nr_args++;
	}
	arg_v[nr_args] = NULL;
	va_end(args);

	dirty = unsafeIRDirty_0_N(0, name, ptr, arg_v);
	addStmtToIRSB(irsb, IRStmt_Dirty(dirty) );
}

static int
fetch_tag(unsigned long addr, struct type_tag *type)
{
	unsigned long h = hash_ptr((void *)(addr - (addr % ADDR_REGION_SIZE)));
	struct address_hash_entry **pprev, *e;
	pprev = &address_hash_heads[h];
	e = *pprev;
	while (e && e->addr != addr) {
		pprev = &e->next;
		e = *pprev;
	}
	if (!e)
		return 0;
	*pprev = e->next;
	e->next = address_hash_heads[h];
	address_hash_heads[h] = e;
	if (type) {
		*type = e->tag;
		type->offset += addr % ADDR_REGION_SIZE;
	}
	return 1;
}

static void
fetch_range(const struct store_hash_entry *e, int i, struct range *out)
{
	tl_assert(i < e->nr_ranges);
	if (i == 0)
		*out = e->range1;
	else
		*out = e->out_of_line_ranges[i-1];
}

static void
store_range(struct store_hash_entry *e, int i, const struct range *r)
{
	tl_assert(i < e->nr_ranges);
	if (i == 0)
		e->range1 = *r;
	else
		e->out_of_line_ranges[i-1] = *r;
}

/* Walk over the list of ranges and try to merge any which are
 * contiguous. */
static int
compact_ranges(struct store_hash_entry *e)
{
	int i;
	int j;
	struct range r1;
	struct range r2;
	int done_something = 0;

	for (i = 0; i < e->nr_ranges; i++) {
		fetch_range(e, i, &r1);
		for (j = i + 1; j < e->nr_ranges; j++) {
			fetch_range(e, j, &r2);
			if (r1.t.allocation_rip != r2.t.allocation_rip ||
			    (r1.t.allocation_size != r2.t.allocation_size &&
			     !(r1.t.allocation_size < 0 &&
			       r2.t.allocation_size < 0) ) )
				continue;
			if (r1.t.offset > r2.end ||
			    r2.t.offset > r1.end)
				continue;

			/* These can be merged. */
			done_something = 1;
			if (r1.t.offset > r2.t.offset)
				r1.t.offset = r2.t.offset;
			if (r1.end < r2.end)
				r1.end = r2.end;
			store_range(e, i, &r1);
			VG_(memmove)(e->out_of_line_ranges + j,
				     e->out_of_line_ranges + j + 1,
				     sizeof(e->out_of_line_ranges[0]) *
				     (e->nr_ranges - j - 1));
			e->nr_ranges--;
			j--;
		}
	}
	return done_something;
}

static int
log_write_here(unsigned long addr, unsigned long rip, unsigned size, const struct address_hash_entry *ahe)
{
	unsigned long hash = hash_store_addr(rip);
	struct store_hash_entry *e;
	struct range rng;
	int x;

	e = store_hash_heads[hash];
	while (e && e->rip != rip)
		e = e->next;
	if (e && e->nr_ranges == 0) {
		/* This is a special entry which indicates that we
		   should examine further up the call stack. */
		return 0;
	}
	rng.t = ahe->tag;
	rng.t.offset += addr % ADDR_REGION_SIZE;
	rng.end = rng.t.offset + size;
	if (!e) {
		/* First store issued by this instruction */
		e = VG_(malloc)("store_hash_entry", sizeof(*e));
		e->rip = rip;
		e->nr_ranges = 1;
		e->range1 = rng;
		e->next = store_hash_heads[hash];
		store_hash_heads[hash] = e;
		return 1;
	}

retry:
	if (rng.t.allocation_rip  == e->range1.t.allocation_rip &&
	    (rng.t.allocation_size == e->range1.t.allocation_size ||
	     (rng.t.allocation_size < 0 && e->range1.t.allocation_size < 0)) &&
	    rng.end               >= e->range1.t.offset &&
	    rng.t.offset          <= e->range1.end) {
		if (rng.t.offset < e->range1.t.offset)
			e->range1.t.offset = rng.t.offset;
		if (rng.end > e->range1.end)
			e->range1.end = rng.end;
		return 1;
	}
	for (x = 0; x < e->nr_ranges - 1; x++) {
		if (rng.t.allocation_rip  == e->out_of_line_ranges[x].t.allocation_rip &&
		    (rng.t.allocation_size == e->out_of_line_ranges[x].t.allocation_size ||
		     (rng.t.allocation_size < 0 && e->out_of_line_ranges[x].t.allocation_size < 0) )&&
		    rng.end               >= e->out_of_line_ranges[x].t.offset &&
		    rng.t.offset          <= e->out_of_line_ranges[x].end) {
			if (rng.t.offset < e->out_of_line_ranges[x].t.offset)
				e->out_of_line_ranges[x].t.offset = rng.t.offset;
			if (rng.end > e->out_of_line_ranges[x].end)
				e->out_of_line_ranges[x].end = rng.end;
			return 1;
		}
	}
	if (e->nr_ranges == MAX_RANGES_PER_STORE) {
		if (compact_ranges(e))
			goto retry;

		/* Whoops.  This instruction appears to write to too
		   many distinct types, so it's probably e.g. part of
		   a memset or equivalent.  Use the enclosing function
		   instead. */
		VG_(printf)("%lx becomes memset-like.\n", rip);
		VG_(printf)("%lx:%lx:%x:%x ",
			    e->range1.t.allocation_rip,
			    e->range1.t.allocation_size,
			    e->range1.t.offset,
			    e->range1.end);
		for (x = 0; x < e->nr_ranges - 1; x++)
			VG_(printf)("%lx:%lx:%x:%x ",
				    e->out_of_line_ranges[x].t.allocation_rip,
				    e->out_of_line_ranges[x].t.allocation_size,
				    e->out_of_line_ranges[x].t.offset,
				    e->out_of_line_ranges[x].end);
		VG_(printf)("\n");
		e->nr_ranges = 0;
		return 0;
	}

	if (e->nr_ranges == 1) {
		e->out_of_line_ranges = VG_(malloc)("out of line ranges",
						    sizeof(*e->out_of_line_ranges));
	} else {
		e->out_of_line_ranges = VG_(realloc)("out of line tags",
						     e->out_of_line_ranges,
						     sizeof(*e->out_of_line_ranges) *
						     e->nr_ranges);
	}
	e->out_of_line_ranges[e->nr_ranges-1] = rng;
	e->nr_ranges++;
	return 1;
}

static void
log_write(unsigned long addr, unsigned long rip, unsigned size, struct address_hash_entry *ahe)
{
	int r;
	ThreadId tid;
	struct thread_extra_data *ted;

	/* Try accounting to this instruction. */
	if (log_write_here(addr, rip, size, ahe))
		return;

	/* This instruction looks like it's in a memset()-like utility
	   function, so uninteresting.  Account to the callers. */
	tid = VG_(get_running_tid)();
	for (ted = thread_extra_heads[tid % NR_THREAD_EXTRA_HEADS];
	     ted && ted->tid != tid;
	     ted = ted->next)
		;
	if (!ted) {
		/* Stores which happen before the first function call
		   are generally pretty damn uninteresting. */
		return;
	}
	for (r = ted->nr_stack_slots - 1; r >= 0; r--) {
		if (log_write_here(addr, ted->stack[r], size, ahe))
			return;
	}

	/* Uh oh.  The entire program is memset()-like.  We're
	 * screwed. */
	VG_(printf)("Entire program is memset-like?\n");
	VG_(printf)("%lx ", rip);
	for (r = 0; r < ted->nr_stack_slots; r++)
		VG_(printf)("%lx ", ted->stack[r]);
	VG_(printf)("\n");
}

/* If @value points at the heap, and the location it points it is
   currently thread-private, redesignate it as process-global, walking
   any pointers in the allocation and redesignating them as well. */
static void
consider_deprivatising(unsigned long value)
{
	struct address_hash_entry *e = find_address_hash_entry(value);
	unsigned long alloc_sz;
	unsigned long alloc_start;
	unsigned long ptr;
	unsigned long ptr2;

	if (!e || !e->is_private)
		return;

	/* Now go and do the privatisation step. */
	alloc_start = value - e->tag.offset;
	alloc_sz = e->tag.allocation_size;

	/* Deprivatise the entire allocation.  We do this in two steps to
	   help avoid unnecessary recursion later. */
	for (ptr = alloc_start; ptr < alloc_start + alloc_sz; ptr += 8) {
		e = find_address_hash_entry(ptr);
		tl_assert(e);
		e->is_private = 0;
	}

	/* Now privatise everything which is reachable from this
	 * block, recursively. */
	for (ptr = alloc_start; ptr < alloc_start + alloc_sz; ptr += 8) {
		/* This dereference is safe because we know that it's
		   in a block which has been malloc()ed and not
		   free()ed. */
		ptr2 = *(unsigned long *)ptr;
		/* Hopefully the recursion will be nice and shallow... */
		consider_deprivatising(ptr2);
	}
}

static void
do_store(unsigned long addr, unsigned long data, unsigned long size,
	 unsigned long rsp, unsigned long rip)
{
	if (addr < rsp - 128 || addr >= rsp + 8192) {
		struct address_hash_entry *e = find_address_hash_entry(addr);
		if (e)
			log_write(addr, rip, size, e);
		if (size == 8 &&
		    (!e || !e->is_private) &&
		    !(addr % 8))
			consider_deprivatising(data);
	}
	VG_(memcpy)( (void *)addr, &data, size);
}

static void
do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
	  unsigned long rsp, unsigned long rip)
{
	if (addr >= rsp - 128 && addr < rsp + 8192) {
		struct address_hash_entry *e = find_address_hash_entry(addr);
		if (e)
			log_write(addr, rip, 16, e);
		if ((!e || !e->is_private) && !(addr % 8)) {
			consider_deprivatising(x1);
			consider_deprivatising(x2);
		}
	}
	((unsigned long *)addr)[0] = x1;
	((unsigned long *)addr)[1] = x2;
}

static void
constructLoggingStore(IRSB *irsb,
		      IRExpr *addr,
		      IRExpr *data,
		      unsigned long rip)
{
	IRType t = typeOfIRExpr(irsb->tyenv, data);
	IRTemp tmp1, tmp2;
	int is_vector = 0;
	IRTemp rsp;

	rsp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(rsp,
				   IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
	switch (t) {
	case Ity_I8:
	case Ity_I16:
	case Ity_I32:
	case Ity_F32:
	case Ity_F64:
		tmp1 = cast_to_U64(irsb, data);
		add_dirty_call(irsb,
			       "do_store",
			       do_store,
			       addr,
			       IRExpr_RdTmp(tmp1),
			       IRExpr_Const(IRConst_U64(sizeofIRType(t))),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	case Ity_I64:
		add_dirty_call(irsb,
			       "do_store",
			       do_store,
			       addr,
			       data,
			       IRExpr_Const(IRConst_U64(8)),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	case Ity_V128:
		is_vector = 1;
	case Ity_I128:
		tmp1 = newIRTemp(irsb->tyenv, Ity_I64);
		tmp2 = newIRTemp(irsb->tyenv, Ity_I64);
		addStmtToIRSB(
			irsb,
			IRStmt_WrTmp(
				tmp1,
				IRExpr_Unop(
					is_vector ? Iop_V128to64 : Iop_128to64,
					data)));
		addStmtToIRSB(
			irsb,
			IRStmt_WrTmp(
				tmp2,
				IRExpr_Unop(
					is_vector ? Iop_V128HIto64 : Iop_128HIto64,
					data)));
		add_dirty_call(irsb,
			       "do_store2",
			       do_store2,
			       addr,
			       IRExpr_RdTmp(tmp1),
			       IRExpr_RdTmp(tmp2),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	default:
		VG_(tool_panic)("Store of unexpected type\n");
	}
}

static void
log_call(unsigned long ret_addr, unsigned long callee)
{
	ThreadId tid = VG_(get_running_tid)();
	struct thread_extra_data *ted;
	unsigned h = tid % NR_THREAD_EXTRA_HEADS;

	for (ted = thread_extra_heads[h];
	     ted && ted->tid != tid;
	     ted = ted->next)
		;
	if (!ted) {
		ted = VG_(malloc)("thread_extra_data", sizeof(*ted));
		ted->tid = tid;
		ted->next = thread_extra_heads[h];
		ted->nr_stack_slots = 0;
		ted->nr_stack_slots_allocated = 16;
		ted->stack = VG_(malloc)("Thread stack", sizeof(ted->stack[0]) * ted->nr_stack_slots_allocated);
		thread_extra_heads[h] = ted;
	}
	if (ted->nr_stack_slots == ted->nr_stack_slots_allocated) {
		ted->nr_stack_slots_allocated *= 2;
		ted->stack = VG_(realloc)("Thread stack",
					  ted->stack,
					  sizeof(ted->stack[0]) * ted->nr_stack_slots_allocated);
	}
	ted->stack[ted->nr_stack_slots] = ret_addr;
	ted->nr_stack_slots++;
}

static void
log_return(unsigned long to, unsigned long rip)
{
	ThreadId tid = VG_(get_running_tid)();
	struct thread_extra_data *ted;
	unsigned h = tid % NR_THREAD_EXTRA_HEADS;
	int x;

	for (ted = thread_extra_heads[h];
	     ted && ted->tid != tid;
	     ted = ted->next)
		;

	tl_assert(ted);
	for (x = ted->nr_stack_slots - 1; x >= 0; x--) {
		if (ted->stack[x] == to) {
			if (x != ted->nr_stack_slots - 1)
				VG_(printf)("Returning to something other than the calling function; did someone call longjmp?\n");
			ted->nr_stack_slots = x;
			return;
		}
	}
	VG_(printf)("Returning to somewhere we never came from... (%lx)\n", to);
	ted->nr_stack_slots = 0;
}

static IRSB *
ft_instrument(VgCallbackClosure* closure,
	      IRSB* bb,
	      VexGuestLayout* layout,
	      VexGuestExtents* vge,
	      IRType gWordTy,
	      IRType hWordTy)
{
	IRSB *out = deepCopyIRSBExceptStmts(bb);
	int x;
	IRStmt *stmt;
	unsigned long instr_end;
	unsigned long instr_start;

	instr_start = 0xdeadbeefbabe;
	instr_end = 0xf001beefdeadcafe;
	for (x = 0; x < bb->stmts_used; x++) {
		stmt = bb->stmts[x];
		if (stmt->tag != Ist_Store) {
			addStmtToIRSB(out, stmt);
		} else {
			constructLoggingStore(out, stmt->Ist.Store.addr,
					      stmt->Ist.Store.data,
					      instr_start);
		}
		if (stmt->tag == Ist_IMark) {
			instr_start = stmt->Ist.IMark.addr;
			instr_end = stmt->Ist.IMark.addr + stmt->Ist.IMark.len;
		}
	}

	if (out->jumpkind == Ijk_Call)
		add_dirty_call(out,
			       "log_call",
			       log_call,
			       IRExpr_Const(IRConst_U64(instr_end)),
			       out->next,
			       NULL);
	else if (out->jumpkind == Ijk_Ret)
		add_dirty_call(out,
			       "log_return",
			       log_return,
			       out->next,
			       IRExpr_Const(IRConst_U64(instr_end)),
			       NULL);
	return out;
}

struct write_file {
	int fd;
	unsigned buf_prod;
	unsigned char buf[1024];
};

static int
open_write_file(struct write_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(tag_table, VKI_O_WRONLY|VKI_O_CREAT|VKI_O_TRUNC, 0600);
	if (sr.isError)
		return sr.err;
	out->fd = sr.res;
	out->buf_prod = 0;
	return 0;
}

static void
write_file(struct write_file *wf, const void *buf, size_t sz)
{
	unsigned to_copy;
	unsigned x;
	int y;

	while (sz != 0) {
		if (wf->buf_prod == sizeof(wf->buf)) {
			for (x = 0; x < wf->buf_prod; x += y) {
				y = VG_(write)(wf->fd, wf->buf + x, wf->buf_prod - x);
				tl_assert(y > 0);
			}
			wf->buf_prod = 0;
		}

		to_copy = sz;
		if (wf->buf_prod + to_copy >= sizeof(wf->buf))
			to_copy = sizeof(wf->buf) - wf->buf_prod;
		VG_(memcpy)(wf->buf + wf->buf_prod, buf, to_copy);
		wf->buf_prod += to_copy;
		buf = (void *)((unsigned long)buf + to_copy);
		sz -= to_copy;
	}
}

static void
close_write_file(struct write_file *wf)
{
	int x, y;
	for (x = 0; x < wf->buf_prod; x+= y) {
		y = VG_(write)(wf->fd, wf->buf + x, wf->buf_prod - x);
		tl_assert(y > 0);
	}
	VG_(close)(wf->fd);
}

static void
ft_fini(Int exitcode)
{
	/* Walk the store table and output the tag tables. */
	struct write_file wf;
	struct table_site_header tsh;
	struct store_hash_entry *e;
	int x;

	x = open_write_file(&wf, tag_table);
	if (x < 0)
		VG_(tool_panic)("Opening output tag table\n");
	for (x = 0; x < NR_STORE_HASH_HEADS; x++) {
		for (e = store_hash_heads[x]; e; e = e->next) {
			tsh.rip = e->rip;
			tsh.nr_ranges = e->nr_ranges;
			write_file(&wf, &tsh, sizeof(tsh));
			if (tsh.nr_ranges != 0) {
				write_file(&wf, &e->range1, sizeof(e->range1));
				write_file(&wf, e->out_of_line_ranges,
					   sizeof(e->out_of_line_ranges[0]) * (e->nr_ranges - 1));
			}
		}
	}
	close_write_file(&wf);
}

static void
my_free(ThreadId tid, void *p)
{
	clear_allocation_tag(p);
	VG_(cli_free)(p);
}

static void *
my_memalign(ThreadId tid, SizeT align, SizeT n)
{
	void *res;
	if (align < 8)
		align = 8;
	n = (n + 7ul) & ~7ul;

	res = VG_(cli_malloc)(align, n);
	if (res)
		register_allocation(res, n, tid, 0);
	return res;
}

static void *
my_malloc(ThreadId tid, SizeT n)
{
	return my_memalign(tid, 0, n);
}

static void *
my_calloc(ThreadId tid, SizeT nmemb, SizeT size1)
{
	void *buf = my_malloc(tid, nmemb * size1);
	VG_(memset)(buf, 0, nmemb * size1);
	return buf;
}

static void *
my_realloc(ThreadId tid, void *p, SizeT new_size)
{
	void *n;
	if (new_size == 0) {
		my_free(tid, p);
		return NULL;
	}
	if (p == NULL) {
		n = VG_(cli_malloc)(8, new_size);
		if (n)
			register_allocation(n, new_size, tid, 1);
		return n;
	}
	clear_allocation_tag(p);
	n = VG_(cli_realloc)(p, new_size);
	if (n != 0)
		register_allocation(n, new_size, tid, 1);
	return n;
}

static void
ft_load(unsigned long addr, unsigned long size, Char *name)
{
	VG_(printf)("Load %s at %lx\n", name, addr);
}

static void
ft_unload(unsigned long addr, unsigned long size, Char *name)
{
	VG_(printf)("Unload %s from %lx\n", name, addr);
}

static void nl_pre_clo_init(void)
{
   VG_(details_name)            ("Findtypes");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("foo");
   VG_(details_copyright_author)("bar");
   VG_(details_bug_reports_to)  ("bazz");

   /* XXX make this configurable. */
   tag_table = "tag_table.dat";

   VG_(basic_tool_funcs)        (ft_post_clo_init,
                                 ft_instrument,
                                 ft_fini);

   VG_(needs_load_unload)(ft_load, ft_unload);
   VG_(needs_malloc_replacement)(my_malloc,
				 my_malloc,
				 my_malloc,
				 my_memalign,
				 my_calloc,
				 my_free,
				 my_free,
				 my_free,
				 my_realloc,
				 0);
}

VG_DETERMINE_INTERFACE_VERSION(nl_pre_clo_init)
