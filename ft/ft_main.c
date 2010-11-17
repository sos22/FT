/* Based on nullgrind */
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

struct type_tag {
	unsigned long allocation_rip;
	SizeT allocation_size;
	unsigned offset;
};

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
#define MAX_TAGS_PER_STORE 8
struct store_hash_entry {
	struct store_hash_entry *next;
	unsigned long rip;
	struct type_tag tag1; /* The common case is that each store
				 writes precisely one tag, so keep one
				 tag inline. */
	int nr_tags; /* This is zero if we should backtrack another
			level up the call stack. */
	struct type_tag *out_of_line_tags;
};
#define NR_STORE_HASH_HEADS 4097
static struct store_hash_entry *
store_hash_heads[NR_STORE_HASH_HEADS];

static void
build_tag(struct type_tag *t, ThreadId tid, SizeT sz)
{
	Addr stack[2];
	int n;

	t->offset = 0;
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
	sz = e->tag.allocation_size;
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
		tl_assert(e->tag.allocation_size == sz);
		*pprev = e->next;
		VG_(free)(e);
	}
}

static void
register_allocation(void *ptr, SizeT sz, ThreadId tid)
{
	int x;
	struct address_hash_entry *e;
	struct type_tag tag;
	unsigned long h;

	build_tag(&tag, tid, sz);

	for (x = 0; x < sz; x += ADDR_REGION_SIZE) {
		e = VG_(malloc)("address_hash_entry", sizeof(*e));
		e->addr = (unsigned long)ptr + x;
		e->tag = tag;
		e->tag.offset = x;
		h = hash_ptr((void *)e->addr);
		e->next = address_hash_heads[h];
		address_hash_heads[h] = e;
	}
}

static void nl_post_clo_init(void)
{
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
tags_eq(const struct type_tag *a, const struct type_tag *b)
{
	return a->allocation_rip == b->allocation_rip &&
		a->allocation_size == b->allocation_size &&
		a->offset == b->offset;
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
	*type = e->tag;
	type->offset += addr % ADDR_REGION_SIZE;
	return 1;
}

static int
log_write_here(unsigned long addr, unsigned long rip)
{
	struct store_hash_entry *e;
	unsigned long hash = addr;
	struct type_tag tag;
	int x;

	while (hash >= NR_STORE_HASH_HEADS)
		hash = (hash / NR_STORE_HASH_HEADS) ^ (hash % NR_STORE_HASH_HEADS);
	e = store_hash_heads[hash];
	while (e && e->rip != rip)
		e = e->next;
	if (e && e->nr_tags == 0) {
		/* This is a special entry which indicates that we
		   should examine further up the call stack. */
		return 0;
	}
	if (!fetch_tag(addr, &tag)) {
		/* Not a malloc address */
		return 1;
	}
	if (!e) {
		/* First store issued by this instruction */
		e = VG_(malloc)("store_hash_entry", sizeof(*e));
		e->rip = rip;
		e->nr_tags = 1;
		e->tag1 = tag;
		e->next = store_hash_heads[hash];
		store_hash_heads[hash] = e;
		return 1;
	}

	if (tags_eq(&e->tag1, &tag))
		return 1;
	for (x = 0; x < e->nr_tags - 1; x++)
		if (tags_eq(&e->out_of_line_tags[x], &tag))
			return 1;
	if (e->nr_tags == MAX_TAGS_PER_STORE) {
		/* Whoops.  This instruction appears to write to too
		   many distinct types, so it's probably e.g. part of
		   a memset or equivalent.  Use the enclosing function
		   instead. */
		e->nr_tags = 0;
		return 0;
	}

	if (e->nr_tags == 1) {
		e->out_of_line_tags = VG_(malloc)("out of line tags",
						  sizeof(*e->out_of_line_tags));
	} else {
		e->out_of_line_tags = VG_(realloc)("out of line tags",
						   e->out_of_line_tags,
						   sizeof(*e->out_of_line_tags) *
						   e->nr_tags);
	}
	e->out_of_line_tags[e->nr_tags-1] = tag;
	e->nr_tags++;
	return 1;
}

static void
log_write(unsigned long addr, unsigned long rsp)
{
	Addr stack[8];
	int n;
	int r;

	if (addr >= rsp - 128 && addr < rsp + 8192) {
		/* Quickly drop accesses to the stack. */
		return;
	}

	n = VG_(get_StackTrace)(VG_(get_running_tid)(), stack, 8, NULL, NULL, 0);
	for (r = 0; r < n; r++) {
		if (log_write_here(addr, stack[r]))
			return;
	}
	/* This is bad: the stack is apparently too deep for us to do
	   anything with.  Just ignore this store. */
}

static void
do_store(unsigned long addr, unsigned long data, unsigned long size,
	 unsigned long rsp)
{
	log_write(addr, rsp);
	VG_(memcpy)( (void *)addr, &data, size);
}

static void
do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
	  unsigned long rsp)
{
	log_write(addr, rsp);
	((unsigned long *)addr)[0] = x1;
	((unsigned long *)addr)[1] = x2;
}

static void
constructLoggingStore(IRSB *irsb,
		      IRExpr *addr,
		      IRExpr *data)
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
			       NULL);
		break;
	default:
		VG_(tool_panic)("Store of unexpected type\n");
	}
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

	for (x = 0; x < bb->stmts_used; x++) {
		stmt = bb->stmts[x];
		if (stmt->tag != Ist_Store) {
			addStmtToIRSB(out, stmt);
		} else {
			constructLoggingStore(out, stmt->Ist.Store.addr,
					      stmt->Ist.Store.data);
		}
	}
	return out;
}

static void
ft_fini(Int exitcode)
{
	/* Walk the store table and output the tag tables. */
	int x;
	int y;
	struct store_hash_entry *e;

	for (x = 0; x < NR_STORE_HASH_HEADS; x++) {
		for (e = store_hash_heads[x]; e; e = e->next) {
			if (e->nr_tags == 0)
				continue;
			VG_(printf)("%016lx\t%016lx:%lx:%x\t",
				    e->rip,
				    e->tag1.allocation_rip,
				    e->tag1.allocation_size,
				    e->tag1.offset);
			for (y = 0; y < e->nr_tags - 1; y++) {
				VG_(printf)("%016lx:%lx:%x\t",
					    e->out_of_line_tags[y].allocation_rip,
					    e->out_of_line_tags[y].allocation_size,
					    e->out_of_line_tags[y].offset);
			}
			VG_(printf)("\n");
		}
	}
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
	if (align < 16)
		align = 16;
	n = (n + 15ul) & ~15ul;

	res = VG_(cli_malloc)(align, n);
	if (!res)
		return NULL;
	register_allocation(res, n, tid);
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
	void *buf = my_malloc(8, nmemb * size1);
	VG_(memset)(buf, 0, nmemb * size1);
	return buf;
}

static void *
my_realloc(ThreadId tid, void *p, SizeT new_size)
{
	void *n;
	clear_allocation_tag(p);
	n = VG_(cli_realloc)(p, new_size);
	if (n != 0)
		register_allocation(n, new_size, tid);
	return n;
}

static void nl_pre_clo_init(void)
{
   VG_(details_name)            ("Findtypes");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("foo");
   VG_(details_copyright_author)("bar");
   VG_(details_bug_reports_to)  ("bazz");

   VG_(basic_tool_funcs)        (nl_post_clo_init,
                                 ft_instrument,
                                 ft_fini);

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
