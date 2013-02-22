#include <sys/types.h>

#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_xarray.h"
#include "pub_tool_clientstate.h"
#include "pub_tool_options.h"

#include "libvex_guest_offsets.h"

#include "valgrind.h"

#define PAGE_SIZE (4096ul)

#define NOISY 0

struct write_file {
	int fd;
	unsigned long offset;
	unsigned long written;
	unsigned buf_prod;
	unsigned char buf[1024];
};
struct read_file {
	int fd;
	unsigned buf_prod;
	unsigned buf_cons;
	unsigned char buf[1024];
};

struct rip_entry {
	unsigned long content:63;
	unsigned long is_private:1;
};

struct rip_set {
	int nr_entries;
	int nr_entries_allocated; /* including entry0. */
	struct rip_entry entry0;
	struct rip_entry *entry1N;
};

struct rip_set_pair {
	struct rip_set stores;
	struct rip_set loads;
};

struct alias_table_entry {
	struct alias_table_entry *next;
	struct rip_entry rip;
	struct rip_set_pair aliases_with;
};

struct addr_hash_entry {
	struct addr_hash_entry *next;
	unsigned long addr;
	struct rip_set_pair content;
};

#define NR_AT_HEADS 32769
struct alias_table {
	struct alias_table_entry *heads[NR_AT_HEADS];
};

static struct alias_table
global_alias_table;
static int
stack_is_private = 1;
static int
i_am_multithreaded;
#define NR_ADDR_HASH_HEADS 100271
static struct addr_hash_entry *
addr_hash_heads[NR_ADDR_HASH_HEADS];
static Char *
output_fname;
static unsigned long
bb_cntr;
static unsigned long
periodic_work_period;

static void do_store(unsigned long addr, unsigned long data, unsigned long size,
		     unsigned long rip);
static void do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
		      unsigned long rip);
static int memory_location_is_private(unsigned long addr);
static void make_memory_location_public(unsigned long addr);

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


static void
constructLoggingStore(IRSB *irsb,
		      IRExpr *addr,
		      IRExpr *data,
		      unsigned long rip)
{
	IRType t = typeOfIRExpr(irsb->tyenv, data);
	IRTemp tmp1, tmp2;
	int is_vector = 0;

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
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	default:
		VG_(tool_panic)("Store of unexpected type\n");
	}
}

static IRSB *
log_stores(IRSB *bb)
{
	IRSB *out = deepCopyIRSBExceptStmts(bb);
	int x;
	IRStmt *stmt;
	unsigned long instr_start;

	instr_start = 0xcafebabedeadbeef;
	for (x = 0; x < bb->stmts_used; x++) {
		stmt = bb->stmts[x];
		if (stmt->tag != Ist_Store) {
			addStmtToIRSB(out, stmt);
		} else {
			constructLoggingStore(out,
					      stmt->Ist.Store.addr,
					      stmt->Ist.Store.data,
					      instr_start);
		}
		if (stmt->tag == Ist_IMark)
			instr_start = stmt->Ist.IMark.addr;
	}
	return out;
}

static int
open_write_file(struct write_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(fname, VKI_O_WRONLY|VKI_O_CREAT|VKI_O_TRUNC, 0600);
	if (sr.isError)
		return sr.err;
	out->fd = sr.res;
	out->buf_prod = 0;
	out->offset = 0;
	out->written = 0;
	return 0;
}

static void
write_file(struct write_file *wf, const void *buf, size_t sz)
{
	unsigned to_copy;
	unsigned x;
	int y;

	wf->offset += sz;
	while (sz != 0) {
		if (wf->buf_prod == sizeof(wf->buf)) {
			for (x = 0; x < wf->buf_prod; x += y) {
				y = VG_(write)(wf->fd, wf->buf + x, wf->buf_prod - x);
				tl_assert(y > 0);
				wf->written += y;
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
		wf->written += y;
	}
	VG_(close)(wf->fd);
}

static int
open_read_file(struct read_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(fname, VKI_O_RDONLY, 0600);
	if (sr.isError) {
		return sr.err;
	}
	out->fd = sr.res;
	out->buf_prod = 0;
	out->buf_cons = 0;
	return 0;
}

static int
read_file(struct read_file *rf, void *buf, size_t sz)
{
	unsigned to_copy;
	unsigned rd;
	unsigned offst;

	offst = 0;
	while (offst < sz) {
		to_copy = rf->buf_prod - rf->buf_cons;
		if (to_copy + offst > sz) {
			to_copy = sz - offst;
		}
		if (to_copy == 0) {
			VG_(memmove)(rf->buf, rf->buf + rf->buf_cons, rf->buf_prod - rf->buf_cons);
			rf->buf_prod -= rf->buf_cons;
			rf->buf_cons = 0;
			rd = VG_(read)(rf->fd, (void *)((unsigned long)rf->buf + rf->buf_prod), sizeof(rf->buf) - rf->buf_prod);
			if (rd == 0) {
				/* Hit EOF */
				return -1;
			}
			if (rd < 0) {
				/* Error reading file */
				VG_(printf)("Error %d reading file\n", rd);
				VG_(tool_panic)((Char *)"can't read file");
			}
			rf->buf_prod += rd;
		}
		VG_(memcpy)((void *)((unsigned long)buf + offst),
			    (const void *)((unsigned long)rf->buf + rf->buf_cons),
			    to_copy);
		offst += to_copy;
		rf->buf_cons += to_copy;
	}
	return 0;
}

static void
close_read_file(struct read_file *rf)
{
	VG_(close)(rf->fd);
}


static unsigned
hash_rip(const struct rip_entry *re)
{
	return (re->content >> 33) ^ (re->content);
}

static int
rips_equal(const struct rip_entry *re1, const struct rip_entry *re2)
{
	return re1->content == re2->content && re1->is_private == re2->is_private;
}

static int
rips_equal_modulo_privateness(const struct rip_entry *re1, const struct rip_entry *re2)
{
	return re1->content == re2->content;
}

static int
rip_less_than(const struct rip_entry *re1, const struct rip_entry *re2)
{
	return re1->content < re2->content;
}

static void
copy_rip_entry(struct rip_entry *dest, const struct rip_entry *src)
{
	*dest = *src;
}

static void
write_rip_entry(struct write_file *output, const struct rip_entry *re)
{
	write_file(output, re, sizeof(*re));
}

static void
read_rip_entry(struct read_file *input, struct rip_entry *re)
{
	if (read_file(input, re, sizeof(*re)) != 0) {
		VG_(tool_panic)("Reading RIP entry");
	}
}

static void
add_address_to_set(struct rip_set *set, const struct rip_entry *entry)
{
	int low, high;
	struct rip_entry *ool;

	if (set->nr_entries == 0) {
		copy_rip_entry(&set->entry0, entry);
	} else if (set->nr_entries == 1) {
		if (rips_equal(&set->entry0, entry))
			return;
		set->nr_entries_allocated = 2;
		ool = VG_(malloc)("address set OOL", sizeof(set->entry1N[0]) * (set->nr_entries_allocated-1));
		VG_(memset)(ool, 0, sizeof(set->entry1N[0]) * (set->nr_entries_allocated-1));
		if (rip_less_than(entry, &set->entry0)) {
			ool[0] = set->entry0;
			copy_rip_entry(&set->entry0, entry);
		} else {
			copy_rip_entry(&ool[0], entry);
		}
		set->entry1N = ool;
	} else {
		if (rips_equal(&set->entry0, entry))
			return;
		if (rip_less_than(entry, &set->entry0)) {
			if (set->nr_entries_allocated == set->nr_entries) {
				set->nr_entries_allocated *= 4;
				set->entry1N = VG_(realloc)("address set OOL",
							    set->entry1N,
							    sizeof(set->entry1N[0]) * (set->nr_entries_allocated-1));
			}
			VG_(memmove)(set->entry1N + 1,
				     set->entry1N,
				     sizeof(set->entry1N[0]) *
				     (set->nr_entries - 1));
			set->entry1N[0] = set->entry0;
			copy_rip_entry(&set->entry0, entry);
		} else {
			/* Binary chop to find the place to insert.
			   The indexes point at places *between* the
			   entries in the list, so that an index of 5
			   points between entry1N[4] and entry1N[5],
			   and index 0 points at the very start of the
			   list (before entry1N[0]).  Our invariant is
			   then that everything left of @low is less
			   than @addr, and everything right of @high
			   is greater than it. */
			low = 0;
			high = set->nr_entries - 1;
			while (low != high) {
				int probe = (low + high) / 2;
				tl_assert(low < high);
				/*
				    . . . . . A . B . . . .
				                ^
						|
					      probe

				    We compare addr to B.  If addr < B
				    then we know that everything to
				    the right of B is greater than
				    addr, and so we can set high equal
				    to probe.  If addr > B, then we know
				    that B and everything to the left of it
				    is less than addr, and so we can set low
				    to probe plus one.  We therefore maintain
				    the invariant.

				    For progress, we need to know that
				    either low or high will change
				    every time around the loop, and that
				    at the end of the loop low == high.
				    Demonstrating that they change is easy:
				    either high is set equal to probe, or
				    low is set equal to probe + 1.
				    We know that high != probe, because
				    high > low and probe = (high + low)/2
				    rounding down.  We also know that
				    low != probe + 1, because probe >= low,
				    so that's all nice and easy.

				    So the hard part is proving that we
				    don't overshoot i.e. that low <= high
				    after all of this is done.

				    Two bits:

				    -- First branch: need to prove low
				       <= probe, but that's trivial.

				    -- Second branch: need to probe
				       probe + 1 <= high, i.e. probe < high,
				       which is also true by the definition
				       of probe.

				    So this will terminate, and will
				    terminate with the right answer.
				*/
				if (rip_less_than(entry, &set->entry1N[probe])) {
					tl_assert(high != probe);
					high = probe;
				} else if (rips_equal(&set->entry1N[probe], entry)) {
					return;
				} else {
					tl_assert(low != probe + 1);
					tl_assert(high != probe);
					low = probe + 1;
				}
			}

			tl_assert(low == high);
			if (set->nr_entries_allocated == set->nr_entries) {
				set->nr_entries_allocated *= 4;
				set->entry1N = VG_(realloc)("address set OOL",
							    set->entry1N,
							    sizeof(set->entry1N[0]) * (set->nr_entries_allocated-1));
			}
			VG_(memmove)(set->entry1N + low + 1,
				     set->entry1N + low,
				     sizeof(set->entry1N[0]) * (set->nr_entries - 1 - low));
			copy_rip_entry(set->entry1N + low, entry);
		}
	}
	set->nr_entries++;
}

static void
init_rip_entry(struct rip_entry *here, unsigned long rip, int private)
{
	here->content = rip;
	here->is_private = private;
}

static void
add_current_address_to_set(struct rip_set *set, unsigned long _addr, int private)
{
	struct rip_entry here;
	tl_assert(_addr != 0);
	init_rip_entry(&here, _addr, private);
	add_address_to_set(set, &here);
}

static unsigned
hash_address(unsigned long addr)
{
	addr /= 32;
	while (addr > NR_ADDR_HASH_HEADS)
		addr = (addr % NR_ADDR_HASH_HEADS) ^ (addr / NR_ADDR_HASH_HEADS);
	return addr;
}

static struct addr_hash_entry *
find_addr_hash_entry(unsigned long addr)
{
	unsigned hash;
	struct addr_hash_entry *cursor, **pprev;
	addr -= addr % 8;
	hash = hash_address(addr);
	pprev = &addr_hash_heads[hash];
	for (cursor = *pprev; cursor && cursor->addr != addr; pprev = &cursor->next, cursor = *pprev)
		;
	if (cursor) {
		*pprev = cursor->next;
		cursor->next = addr_hash_heads[hash];
		addr_hash_heads[hash] = cursor;
		return cursor;
	}
	cursor = VG_(malloc)("addr_hash_entry", sizeof(*cursor));
	cursor->next = addr_hash_heads[hash];
	cursor->addr = addr;
	cursor->content.stores.nr_entries = 0;
	cursor->content.loads.nr_entries = 0;
	addr_hash_heads[hash] = cursor;

	return cursor;
}

static void
log_store(unsigned long rip, unsigned long addr, int private)
{
	struct addr_hash_entry *ahe = find_addr_hash_entry(addr);
	add_current_address_to_set(&ahe->content.stores, rip, private);
}

struct stack_data {
	unsigned long start;
	unsigned long end;
};

static struct stack_data *
get_current_thread_stack_data(void)
{
	static struct stack_data sd[VG_N_THREADS];
	return &sd[VG_(get_running_tid)()];
}

static int
is_stack(unsigned long addr)
{
	struct stack_data *sd;
	sd = get_current_thread_stack_data();
	if (addr >= sd->start && addr <= sd->end)
		return 1;
	else
		return 0;
}

static void
do_store(unsigned long addr, unsigned long data, unsigned long size, unsigned long rip)
{
	int stack = is_stack(addr);
	if (!stack) {
		log_store(rip, addr, memory_location_is_private(addr) || !i_am_multithreaded);
	}
	if ((!stack_is_private || !stack) && size == 8) {
		make_memory_location_public(data);
	}
	VG_(memcpy)( (void *)addr, &data, size);
}

static void
do_store2(unsigned long addr, unsigned long x1, unsigned long x2, unsigned long rip)
{
	do_store(addr, x1, 8, rip);
	do_store(addr + 8, x2, 8, rip);
}

static void
do_log_load(unsigned long addr, unsigned long rip)
{
	struct addr_hash_entry *ahe;
	if (is_stack(addr))
		return;
	ahe = find_addr_hash_entry(addr);
	add_current_address_to_set(&ahe->content.loads, rip, memory_location_is_private(addr) || !i_am_multithreaded);
}

static void
log_this_load(IRSB *irsb, IRExpr *addr, unsigned long rip)
{
	if (addr->tag != Iex_RdTmp) {
		IRTemp t = newIRTemp(irsb->tyenv, Ity_I64);
		addStmtToIRSB(irsb,
			      IRStmt_WrTmp(t, addr));
		addr = IRExpr_RdTmp(t);
	}
	add_dirty_call(irsb, "log_load", do_log_load, addr,
		       IRExpr_Const(IRConst_U64(rip)),
		       NULL);
}

static void
log_loads_expr(IRSB *irsb, IRExpr *expr, unsigned long rip)
{
	switch (expr->tag) {
	case Iex_Binder:
		break;
	case Iex_Get:
		break;
	case Iex_GetI:
		log_loads_expr(irsb, expr->Iex.GetI.ix, rip);
		break;
	case Iex_RdTmp:
		break;

		/* Note fall-through */
	case Iex_Qop:
		log_loads_expr(irsb, expr->Iex.Qop.arg4, rip);
	case Iex_Triop:
		log_loads_expr(irsb, expr->Iex.Triop.arg3, rip);
	case Iex_Binop:
		log_loads_expr(irsb, expr->Iex.Binop.arg2, rip);
	case Iex_Unop:
		log_loads_expr(irsb, expr->Iex.Unop.arg, rip);
		break;

	case Iex_Load:
		log_loads_expr(irsb, expr->Iex.Load.addr, rip);
		log_this_load(irsb, expr->Iex.Load.addr, rip);
		break;

	case Iex_Const:
		break;
	case Iex_CCall: {
		int x;
		for (x = 0; expr->Iex.CCall.args[x]; x++)
			log_loads_expr(irsb, expr->Iex.CCall.args[x], rip);
		break;
	}
	case Iex_Mux0X:
		log_loads_expr(irsb, expr->Iex.Mux0X.cond, rip);
		log_loads_expr(irsb, expr->Iex.Mux0X.expr0, rip);
		log_loads_expr(irsb, expr->Iex.Mux0X.exprX, rip);
		break;
	}
}

static void
do_log_change_rsp(unsigned long old, unsigned long new)
{
	struct stack_data *sd = get_current_thread_stack_data();
	unsigned long new_round_up = (new + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);

	if (old - new >= 4ul << 20 && new - old >= 4ul << 20) {
		/* Arbitrarily decree that moving the stack more than
		   4MiB in one go indicates that you're switching to a
		   new stack. */
		VG_(printf)("Thread %d switched stacks (%lx -> %lx)\n",
			    VG_(get_running_tid)(), old, new);
		sd->start = new - 128;
		sd->end = new_round_up;
		return;
	}

	sd->start = new - 128;
	if (sd->end < new_round_up)
		sd->end = new_round_up;
}

static void
log_change_rsp(IRSB *irsb, IRExpr *new_value)
{
	IRTemp old_rsp_tmp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(old_rsp_tmp,
				   IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
	if (new_value->tag != Iex_RdTmp) {
		IRTemp t = newIRTemp(irsb->tyenv, Ity_I64);
		addStmtToIRSB(irsb,
			      IRStmt_WrTmp(t, new_value));
		new_value = IRExpr_RdTmp(t);
	}
	add_dirty_call(irsb, "log_change_rsp", do_log_change_rsp,
		       IRExpr_RdTmp(old_rsp_tmp),
		       new_value,
		       NULL);
}

static void
periodic_cb(void)
{
	VG_(printf)("Periodic callback invoked, cntr %ld\n", bb_cntr);
	bb_cntr = periodic_work_period;
}

static IRSB *
log_loads(IRSB *inp)
{
	IRSB *out = deepCopyIRSBExceptStmts(inp);
	int x;
	IRStmt *stmt;
	unsigned long instr_start;
	IRTemp addr_tmp;
	IRTemp cntr_tmp;
	IRTemp cntr2_tmp;
	IRTemp guard_tmp;
	IRDirty *run_period;

	if (periodic_work_period != 0) {
		/* Arrange for the periodic callback to run every $N
		 * basic blocks. */
		addr_tmp = newIRTemp(out->tyenv, Ity_I64);
		cntr_tmp = newIRTemp(out->tyenv, Ity_I64);
		cntr2_tmp = newIRTemp(out->tyenv, Ity_I64);
		guard_tmp = newIRTemp(out->tyenv, Ity_I1);
		addStmtToIRSB(
			out,
			IRStmt_WrTmp(
				addr_tmp,
				IRExpr_Const(
					IRConst_U64((unsigned long)&bb_cntr))));
		addStmtToIRSB(
			out,
			IRStmt_WrTmp(
				cntr_tmp,
				IRExpr_Load(
					Iend_LE,
					Ity_I64,
					IRExpr_RdTmp(addr_tmp))));
		addStmtToIRSB(
			out,
			IRStmt_WrTmp(
				cntr2_tmp,
				IRExpr_Binop(
					Iop_Sub64,
					IRExpr_RdTmp(cntr_tmp),
					IRExpr_Const(
						IRConst_U64(1)))));
		addStmtToIRSB(
			out,
			IRStmt_Store(
				Iend_LE,
				IRExpr_RdTmp(addr_tmp),
				IRExpr_RdTmp(cntr2_tmp)));
		addStmtToIRSB(
			out,
			IRStmt_WrTmp(
				guard_tmp,
				IRExpr_Binop(
					Iop_CmpEQ64,
					IRExpr_RdTmp(cntr2_tmp),
					IRExpr_Const(
						IRConst_U64(0)))));
		run_period = unsafeIRDirty_0_N(
			0,
			(HChar *)"periodic_cb",
			periodic_cb,
			mkIRExprVec_0());
		run_period->guard = IRExpr_RdTmp(guard_tmp);
		addStmtToIRSB(
			out,
			IRStmt_Dirty(run_period));
	}

	instr_start = 0xdeadbabebeefface;
	for (x = 0; x < inp->stmts_used; x++) {
		stmt = inp->stmts[x];
		switch (stmt->tag) {
		case Ist_IMark:
			instr_start = stmt->Ist.IMark.addr;
			break;
		case Ist_Put:
			log_loads_expr(out, stmt->Ist.Put.data, instr_start);
			if (stmt->Ist.Put.offset == OFFSET_amd64_RSP)
				log_change_rsp(out, stmt->Ist.Put.data);
			break;
		case Ist_PutI:
			log_loads_expr(out, stmt->Ist.PutI.ix, instr_start);
			log_loads_expr(out, stmt->Ist.PutI.data, instr_start);
			break;
		case Ist_WrTmp:
			log_loads_expr(out, stmt->Ist.WrTmp.data, instr_start);
			break;
		case Ist_Store:
			log_loads_expr(out, stmt->Ist.Store.addr, instr_start);
			log_loads_expr(out, stmt->Ist.Store.data, instr_start);
			break;
		case Ist_Dirty: {
			int y;
			log_loads_expr(out, stmt->Ist.Dirty.details->guard, instr_start);
			for (y = 0; stmt->Ist.Dirty.details->args[y]; y++)
				log_loads_expr(out, stmt->Ist.Dirty.details->args[y], instr_start);
			break;
		}
		case Ist_Exit:
			log_loads_expr(out, stmt->Ist.Exit.guard, instr_start);
			break;
		default:
			break;
		}
		addStmtToIRSB(out, stmt);
	}
	return out;
}

static void
ft2_post_clo_init(void)
{
	if (!output_fname) {
		VG_(tool_panic)((Char *)"need to know where to put the output!\n");
	}
	bb_cntr = periodic_work_period;
}

static IRSB *
ft2_instrument(VgCallbackClosure* closure,
	       IRSB* bb,
	       VexGuestLayout* layout,
	       VexGuestExtents* vge,
	       IRType gWordTy,
	       IRType hWordTy)
{
	return log_loads(log_stores(bb));
}

static const struct rip_entry *
get_set_entry(const struct rip_set *se, int idx)
{
	if (idx == 0)
		return &se->entry0;
	else
		return &se->entry1N[idx - 1];
}

static void
clear_private_flag(struct rip_entry *re)
{
	re->is_private = 0;
}

static struct alias_table_entry *
find_alias_table_entry(struct alias_table *at, const struct rip_entry *re)
{
	unsigned long hash = hash_rip(re);
	unsigned head = hash % NR_AT_HEADS;
	struct alias_table_entry *cursor;
	for (cursor = at->heads[head]; cursor; cursor = cursor->next) {
		if (rips_equal_modulo_privateness(&cursor->rip, re))
			return cursor;
	}
	cursor = VG_(malloc)("alias_table_entry", sizeof(*cursor));
	cursor->next = at->heads[head];
	copy_rip_entry(&cursor->rip, re);
	clear_private_flag(&cursor->rip);
	VG_(memset)(&cursor->aliases_with, 0, sizeof(cursor->aliases_with));
	at->heads[head] = cursor;
	return cursor;
}

static void
merge_rip_sets(struct rip_set *out, const struct rip_set *inp)
{
	int i;
	for (i = 0; i < inp->nr_entries; i++)
		add_address_to_set(out, get_set_entry(inp, i));
}


/* Add the set @s to the global aliasing table.  Zap it to an empty
   set at the same time. */
static void
fold_set_to_alias_table(struct alias_table *at, struct rip_set_pair *s)
{
	int i;
	struct alias_table_entry *ate;
	for (i = 0; i < s->loads.nr_entries; i++) {
		ate = find_alias_table_entry(at, get_set_entry(&s->loads, i));
		merge_rip_sets(&ate->aliases_with.loads, &s->loads);
		merge_rip_sets(&ate->aliases_with.stores, &s->stores);
	}
	for (i = 0; i < s->stores.nr_entries; i++) {
		ate = find_alias_table_entry(at, get_set_entry(&s->stores, i));
		merge_rip_sets(&ate->aliases_with.loads, &s->loads);
		merge_rip_sets(&ate->aliases_with.stores, &s->stores);
	}
	if (s->loads.nr_entries_allocated > 1)
		VG_(free)(s->loads.entry1N);
	if (s->stores.nr_entries_allocated > 1)
		VG_(free)(s->stores.entry1N);
	VG_(memset)(s, 0, sizeof(*s));
}
struct hdr {
	int nr_loads;
	int nr_stores;
};

static void
write_tag_dump(const Char *fname, const struct alias_table *at)
{
	static struct write_file output_file;
	struct alias_table_entry *ate;
	unsigned long magic;
	int err;
	int x;
	int i;

	err = open_write_file(&output_file, fname);
	if (err) {
		VG_(printf)("Cannot open %s: %d\n", fname, err);
		VG_(tool_panic)("Cannot open database");
	}

	magic = 0x1122334455;
	write_file(&output_file, &magic, sizeof(magic));
	for (x = 0; x < NR_AT_HEADS; x++) {
		for (ate = at->heads[x]; ate; ate = ate->next) {
			if (ate->aliases_with.stores.nr_entries > 0 ||
			    ate->aliases_with.loads.nr_entries > 0) {
				struct hdr hdr;
				hdr.nr_loads = ate->aliases_with.loads.nr_entries;
				hdr.nr_stores = ate->aliases_with.stores.nr_entries;
				write_file(&output_file, &hdr, sizeof(hdr));
				write_rip_entry(&output_file, &ate->rip);
				for (i = 0; i < ate->aliases_with.loads.nr_entries; i++) {
					write_rip_entry(&output_file,
							get_set_entry(&ate->aliases_with.loads, i));
				}
				for (i = 0; i < ate->aliases_with.stores.nr_entries; i++) {
					write_rip_entry(&output_file,
							get_set_entry(&ate->aliases_with.stores, i));
				}
			}
		}
	}
	close_write_file(&output_file);
}

static void
ft2_fini(Int exitcode)
{
	int x;
	struct addr_hash_entry *ahe;

	VG_(printf)("ft2_fini() starts\n");

	for (x = 0; x < NR_ADDR_HASH_HEADS; x++) {
		for (ahe = addr_hash_heads[x]; ahe; ahe = ahe->next) {
			fold_set_to_alias_table(&global_alias_table, &ahe->content);
		}
	}

	VG_(printf)("Done folding\n");

	write_tag_dump(output_fname, &global_alias_table);

	VG_(printf)("Finished writing results\n");

}

static void
refresh_tags(struct alias_table *at, void *base, unsigned long size)
{
	unsigned long start = (unsigned long)base & ~7ul;
	unsigned long end = ((unsigned long)base + size + 7) & ~7ul;
	unsigned long ptr;
	struct addr_hash_entry *ahe;
	int x;

	if (size >= NR_ADDR_HASH_HEADS * 16) {
		for (x = 0; x < NR_ADDR_HASH_HEADS; x++) {
			for (ahe = addr_hash_heads[x]; ahe; ahe = ahe->next) {
				if (ahe->addr >= start && ahe->addr < end) {
					fold_set_to_alias_table(at, &ahe->content);
				}
			}
		}
	} else {
		for (ptr = start; ptr < end; ptr += 8) {
			ahe = find_addr_hash_entry(ptr);
			if (ahe) {
				fold_set_to_alias_table(at, &ahe->content);
			}
		}
	}
}

struct memory_tree_entry {
	ThreadId tid;
	unsigned long start;
	unsigned long end;
	struct memory_tree_entry *prev;
	struct memory_tree_entry *next;
};

static struct memory_tree_entry *memory_root;

static struct memory_tree_entry *
new_memory_tree_entry(unsigned long start, unsigned long end)
{
	struct memory_tree_entry *mte = VG_(malloc)("mte_entry", sizeof(*mte));
	mte->tid = VG_(get_running_tid)();
	mte->start = start;
	mte->end = end;
	mte->prev = NULL;
	mte->next = NULL;
	return mte;
}

static void
release_memory_tree_entry(struct memory_tree_entry *mte)
{
	VG_(free)(mte);
}

static void
set_memory_private(unsigned long start, unsigned long end)
{
	struct memory_tree_entry *mte;
	struct memory_tree_entry **mtep;

	if (NOISY) {
		VG_(printf)("%d: set_memory_private(%lx, %lx)\n",
			    VG_(get_running_tid)(), start, end);
	}

	mtep = &memory_root;
	while (*mtep) {
		mte = *mtep;
		if (end <= mte->start) {
			mtep = &mte->prev;
			continue;
		}
		if (start >= mte->end) {
			mtep = &mte->next;
			continue;
		}
		VG_(printf)("Huh? Creating memory region [%lx,%lx), but found [%lx,%lx) already existing\n",
			    start, end, mte->start, mte->end);
		tl_assert(0);
	}
	*mtep = new_memory_tree_entry(start, end);
	(*mtep)->tid = VG_(get_running_tid)();
	return;
}

static void
release_memory_range(unsigned long start, unsigned long end)
{
	struct memory_tree_entry *mte;
	struct memory_tree_entry *cursor;
	struct memory_tree_entry **mtep;

	mtep = &memory_root;
	while (1) {
		mte = *mtep;
		if (!mte) {
			VG_(printf)("Failed to locate memory entry for (%lx,%lx)\n", start, end);
		}
		tl_assert(mte);
		if (mte->start == start || mte->end == end) {
			if (NOISY && mte->tid != VG_INVALID_THREADID) {
				VG_(printf)("%d: release_memory_range(%lx, %lx)\n",
					    VG_(get_running_tid)(),
					    start,
					    end);
			}
			if (mte->tid != VG_INVALID_THREADID &&
			    mte->tid != VG_(get_running_tid)()) {
				VG_(printf)("DOOM: [%lx, %lx) should be private to %d, but was released from %d\n",
					    start, end, mte->tid, VG_(get_running_tid)());
			}
			tl_assert(start == mte->start);
			tl_assert(end == mte->end);
			if (mte->prev) {
				if (mte->next) {
					if (!mte->prev->next) {
						mte->prev->next = mte->next;
						*mtep = mte->prev;
					} else if (!mte->next->prev) {
						mte->next->prev = mte->prev;
						*mtep = mte->next;
					} else {
						for (cursor = mte->prev;
						     cursor->next;
						     cursor = cursor->next)
							;
						cursor->next = mte->next;
						*mtep = mte->prev;
					}
				} else {
					*mtep = mte->prev;
				}
			} else {
				if (mte->next) {
					*mtep = mte->next;
				} else {
					*mtep = NULL;
				}
			}
			release_memory_tree_entry(mte);
			break;
		}
		if (end <= mte->start) {
			mtep = &mte->prev;
			continue;
		}
		if (start >= mte->end) {
			mtep = &mte->next;
			continue;
		}
		VG_(printf)("Huh? Removing [%lx,%lx), found [%lx,%lx)\n",
			    start, end, mte->start, mte->end);
		tl_assert(0);
	}
}

static int
memory_location_is_private(unsigned long addr)
{
	struct memory_tree_entry *mte, **mtep;
	struct memory_tree_entry *r, *rp, *rpp, *rpps, *rps, *rpsp,
		*rpss, *rs, *rsp, *rss, *rspp, *rsps, *rssp;

	mtep = &memory_root;
	while (1) {
		mte = *mtep;
		if (!mte)
			return 0;
		if (addr >= mte->start && addr < mte->end) {
			if (mte->tid != VG_INVALID_THREADID &&
			    mte->tid != VG_(get_running_tid)()) {
				VG_(printf)("DOOM: lookup %lx: found [%lx, %lx) for thread %d, but we are thread %d?\n",
					    addr, mte->start, mte->end, mte->tid, VG_(get_running_tid)());
			}
			return mte->tid != VG_INVALID_THREADID;
		}
		/* Splay */
		r = mte;
		if (addr < mte->start) {
			rp = r->prev;
			if (!rp)
				return 0;
			rpp = rp->prev;
			rps = rp->next;
			if (addr < rp->start) {
				if (!rpp)
					return 0;
				rpps = rpp->next;
				*mtep = rpp;
				rpp->next = r;
				rp->prev = rpps;
			} else if (addr < rp->end) {
				*mtep = rp;
				rp->next = r;
				r->prev = rps;
			} else {
				if (!rps)
					return 0;
				rpss = rps->next;
				rpsp = rps->prev;
				*mtep = rps;
				rps->next = r;
				r->prev = rpss;
				rps->prev = rp;
				rp->next = rpsp;
			}
		} else {
			tl_assert(addr >= mte->end);
			rs = r->next;
			if (!rs)
				return 0;
			rsp = rs->prev;
			rss = rs->next;
			if (addr < rs->start) {
				if (!rsp)
					return 0;
				rspp = rsp->prev;
				rsps = rsp->next;
				*mtep = rsp;
				rsp->prev = r;
				r->next = rspp;
				rsp->next = rs;
				rs->prev = rsps;
			} else if (addr < rs->end) {
				*mtep = rs;
				r->next = rsp;
				rs->prev = r;
			} else {
				if (!rss)
					return 0;
				rssp = rss->prev;
				*mtep = rss;
				rs->prev = r;
				r->next = rsp;
				rss->prev = rs;
				rs->next = rssp;
			}
		}
	}
	asm("ud2\n");
	return 0;
}

static void
make_memory_location_public(unsigned long addr)
{
	struct memory_tree_entry *mte;

	for (mte = memory_root; mte; ) {
		if (addr < mte->start)
			mte = mte->prev;
		else if (addr >= mte->end)
			mte = mte->next;
		else {
			if (NOISY) {
				VG_(printf)("%d: make_memory_location_public(%lx): %lx, %lx\n",
					    VG_(get_running_tid)(),
					    addr,
					    mte->start,
					    mte->end);
			}
			mte->tid = VG_INVALID_THREADID;
			return;
		}
	}
}

static Bool
ft2_client_request(ThreadId tid, UWord *arg_block, UWord *ret)
{
	*ret = 0;
	if (VG_IS_TOOL_USERREQ('F', 'T', arg_block[0]) &&
	    arg_block[0] == VG_USERREQ_TOOL_BASE('F', 'T')) {
		refresh_tags(&global_alias_table,
			     (void *)arg_block[1],
			     arg_block[2]);
		return True;
	} else {
		return False;
	}
}

static void
ft2_create_thread(ThreadId tid, ThreadId child)
{
	if (tid == VG_INVALID_THREADID)
		return;
	i_am_multithreaded = 1;
}

static void
ft2_print_usage(void)
{
	VG_(printf)("\t--output=<fname>     Where to dump the type file\n");
	VG_(printf)("\t--input=<fname>      Tag table to pre-init the global table with\n");
	VG_(printf)("\t--stack-private=yes|no Is the stack thread-private?  Default yes\n");
}

static void
ft2_print_debug_usage(void)
{
}

static int
read_alias_table_entry(struct read_file *rfile, struct alias_table *at)
{
	struct hdr hdr;
	struct rip_entry re;
	struct alias_table_entry *ate;
	int i;

	if (read_file(rfile, &hdr, sizeof(hdr)) < 0) {
		return 0;
	}
	read_rip_entry(rfile, &re);
	ate = find_alias_table_entry(at, &re);
	for (i = 0; i < hdr.nr_loads; i++) {
		read_rip_entry(rfile, &re);
		add_address_to_set(&ate->aliases_with.loads, &re);
	}
	for (i = 0; i < hdr.nr_stores; i++) {
		read_rip_entry(rfile, &re);
		add_address_to_set(&ate->aliases_with.stores, &re);
	}
	return 1;
}

static void
read_tag_dump(const Char *fname)
{
	static struct read_file rfile;
	int err;
	unsigned long magic;

	err = open_read_file(&rfile, fname);
	if (err) {
		VG_(printf)("%d opening %s\n", err, fname);
		VG_(tool_panic)("Cannot read input file");
	}
	if (read_file(&rfile, &magic, sizeof(magic)) != 0 ||
	    magic != 0x1122334455) {
		VG_(printf)("Wrong file format; magic %lx\n", magic);
		VG_(tool_panic)("Bad input");
	}
	while (read_alias_table_entry(&rfile, &global_alias_table)) {
		/* noop */
	}
	close_read_file(&rfile);
}

static Bool
ft2_process_command_line_option(Char *opt)
{
	if (VG_CLO_STREQN(VG_(strlen)("--output")+1, opt, "--output=")) {
		output_fname = opt + VG_(strlen)("--output") + 1;
		return True;
	} else if (VG_CLO_STREQN(VG_(strlen)("--input")+1, opt, "--input=")) {
		read_tag_dump(opt + VG_(strlen)("--input") + 1);
		return True;
	} else VG_BOOL_CLO(opt, "--stack-private", stack_is_private)
	else VG_NUM_CLO(opt, "--period", periodic_work_period)
	else {
		return False;
	}
	return True;
}

#include "pub_tool_hashtable.h"

//------------------------------------------------------------//
//--- Heap management                                      ---//
//------------------------------------------------------------//

// Metadata for heap blocks.  Each one contains a pointer to a bottom-XPt,
// which is a foothold into the XCon at which it was allocated.  From
// HP_Chunks, XPt 'space' fields are incremented (at allocation) and
// decremented (at deallocation).
//
// Nb: first two fields must match core's VgHashNode.
typedef
   struct _HP_Chunk {
      struct _HP_Chunk* next;
      Addr              data;       // Ptr to actual block
      SizeT             req_szB;    // Size requested
   }
   HP_Chunk;

static VgHashTable malloc_list  = NULL;   // HP_Chunks

static void *
new_block(struct alias_table *at, SizeT req_szB, SizeT req_alignB )
{
   HP_Chunk* hc;
   void *p;

   if (req_szB < 0) return NULL;

   p = VG_(cli_malloc)( req_alignB, req_szB );
   if (!p) {
     return NULL;
   }

   // Make new HP_Chunk node, add to malloc_list
   hc           = VG_(malloc)("ms.main.nb.1", sizeof(HP_Chunk));
   hc->req_szB  = req_szB;
   hc->data     = (Addr)p;
   VG_(HT_add_node)(malloc_list, hc);

   refresh_tags(at, p, req_szB);
   set_memory_private((unsigned long)p, (unsigned long)p + req_szB);

   return p;
}

static void *
ms_memalign ( ThreadId tid, SizeT alignB, SizeT szB )
{
	return new_block(&global_alias_table, szB, alignB);
}

static void *
ms_malloc ( ThreadId tid, SizeT szB )
{
	return ms_memalign(tid, VG_(clo_alignment), szB);
}

static void *
ms_calloc ( ThreadId tid, SizeT m, SizeT szB )
{
	void *r = ms_memalign(tid, VG_(clo_alignment), m*szB);
	if (r) {
		VG_(memset)(r, 0, m * szB);
	}
	return r;
}

static void ms_free ( ThreadId tid, void* p )
{
	HP_Chunk *hc = VG_(HT_remove)(malloc_list, (UWord)p);
	release_memory_range((unsigned long)p,
			     (unsigned long)p + hc->req_szB);
	VG_(free)( hc );
	VG_(cli_free)( p );
}

static void* ms_realloc ( ThreadId tid, void* p_old, SizeT new_szB )
{
	void *p_new = VG_(cli_malloc)(VG_(clo_alignment), new_szB);
	HP_Chunk *hc;

	if (!p_new) {
		return NULL;
	}

	hc = VG_(HT_remove)(malloc_list, (UWord)p_old);

	release_memory_range((unsigned long)p_old,
			     (unsigned long)p_old + hc->req_szB);

	if (hc->req_szB < new_szB) {
		VG_(memcpy)(p_new, p_old, hc->req_szB);
	} else {
		VG_(memcpy)(p_new, p_old, new_szB);
	}
	VG_(cli_free)(p_old);

	hc->data     = (Addr)p_new;
	hc->req_szB  = new_szB;

	VG_(HT_add_node)(malloc_list, hc);

	refresh_tags(&global_alias_table, p_new, new_szB);
	set_memory_private((unsigned long)p_new, (unsigned long)p_new + new_szB);

	return p_new;
}

static void ft2_pre_clo_init(void)
{
	VG_(details_name)("FT2");
	VG_(details_version)(NULL);
	VG_(details_description)("foo");
	VG_(details_copyright_author)("me");
	VG_(details_bug_reports_to)(VG_BUGS_TO);

	VG_(basic_tool_funcs)(ft2_post_clo_init, ft2_instrument, ft2_fini);

	VG_(track_pre_thread_ll_create)(ft2_create_thread);

	VG_(needs_command_line_options) (ft2_process_command_line_option,
					 ft2_print_usage,
					 ft2_print_debug_usage);
	VG_(needs_malloc_replacement)  (ms_malloc,
					ms_malloc,
					ms_malloc,
					ms_memalign,
					ms_calloc,
					ms_free,
					ms_free,
					ms_free,
					ms_realloc,
					0 );

	VG_(needs_client_requests)(ft2_client_request);

	malloc_list = VG_(HT_construct)( "Massif's malloc list" );
}

VG_DETERMINE_INTERFACE_VERSION(ft2_pre_clo_init)
