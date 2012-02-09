#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

#include "../ft/io.c"

#define NR_INLINE_RIPS 8

struct rip_entry {
	unsigned long rip;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long content[NR_INLINE_RIPS];
	unsigned long *out_of_line_content;
};

static struct rip_entry thread_callstacks[VG_N_THREADS];

struct hash_entry {
	struct hash_entry *next;
	struct rip_entry rip;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long *entries;
};
#define NR_HASH_HEADS 65537
static struct hash_entry *hash_heads[NR_HASH_HEADS];

static unsigned long
get_re_entry(const struct rip_entry *re, unsigned idx)
{
	if (idx >= NR_INLINE_RIPS)
		return re->out_of_line_content[idx-NR_INLINE_RIPS];
	else
		return re->content[idx];
}

/* advance to the next one in a way which avoids considering any
   cycles in the stack (e.g. recursive functions). */
static int
next_re_idx(const struct rip_entry *re, unsigned long entry)
{
	unsigned long entry2;
	int y;

	for (y = 0; y < re->nr_entries; y++) {
		entry2 = get_re_entry(re, y);
		if (entry2 == entry)
			return y - 1;
	}
	tl_assert(0);
	return -1;
}

static unsigned
hash_rip(const struct rip_entry *re, unsigned long rip)
{
	unsigned long addr = rip;
	unsigned long entry;
	int x;
	int nr_inline = re->nr_entries;
	if (nr_inline > NR_INLINE_RIPS)
		nr_inline = NR_INLINE_RIPS;
	for (x = re->nr_entries - 1; x >= 0; ) {
		entry = get_re_entry(re, x);
		addr = ((addr << 31) | (addr >> 33)) ^ entry;
		x = next_re_idx(re, entry);
	}
	while (addr > NR_HASH_HEADS)
		addr = (addr % NR_HASH_HEADS) ^ (addr / NR_HASH_HEADS);
	return addr;
}

static int
rips_equal(const struct rip_entry *re1, const struct rip_entry *re2, unsigned long rip)
{
	int idx1, idx2;
	unsigned long entry1, entry2;

	if (re1->rip != rip)
		return 0;
	idx1 = re1->nr_entries - 1;
	idx2 = re2->nr_entries - 1;
	while (idx1 >= 0 && idx2 >= 0) {
		entry1 = get_re_entry(re1, idx1);
		entry2 = get_re_entry(re2, idx2);
		if (entry1 != entry2)
			return 0;
		idx1 = next_re_idx(re1, entry1);
		idx2 = next_re_idx(re2, entry2);
	}
	if (idx1 >= 0 || idx2 >= 0)
		return 0;
	return 1;
}

static void
copy_rip_entry(struct rip_entry *dest, const struct rip_entry *src, unsigned long rip)
{
	int nr_inline;

	dest->nr_entries = src->nr_entries;
	if (dest->nr_entries < NR_INLINE_RIPS) {
		dest->nr_entries_allocated = 0;
		nr_inline = dest->nr_entries;
	} else {
		dest->nr_entries_allocated = dest->nr_entries - NR_INLINE_RIPS;
		nr_inline = NR_INLINE_RIPS;
	}
	VG_(memcpy)(dest->content, src->content, sizeof(dest->content[0]) * nr_inline);
	if (dest->nr_entries_allocated != 0) {
		dest->out_of_line_content = VG_(malloc)("rip_entry_content", sizeof(dest->content[0]) * dest->nr_entries_allocated);
		VG_(memcpy)(dest->out_of_line_content, src->out_of_line_content,
			    sizeof(dest->out_of_line_content[0]) * dest->nr_entries_allocated);
	}
	dest->rip = rip;
}

static void
print_rip_entry(const struct rip_entry *re)
{
	int i;
	for (i = 0; i < re->nr_entries && i < NR_INLINE_RIPS; i++)
		VG_(printf)("%lx\n", re->content[i]);
	for ( ; i < re->nr_entries; i++)
		VG_(printf)("%lx\n", re->out_of_line_content[i]);
}

static void
log_call(unsigned long rip, unsigned long is_call, unsigned long callee)
{
	const struct rip_entry *caller = &thread_callstacks[VG_(get_running_tid)()];
	unsigned h = hash_rip(caller, rip);
	struct hash_entry *he;
	unsigned i;

	for (he = hash_heads[h]; he && !rips_equal(&he->rip, caller, rip); he = he->next)
		;
	if (!he) {
		he = VG_(malloc)("hash_entry", sizeof(*he));
		he->next = hash_heads[h];
		copy_rip_entry(&he->rip, caller, rip);
		he->nr_entries = 0;
		he->nr_entries_allocated = 4;
		he->entries = VG_(malloc)("hash_entry->entries",
					  sizeof(he->entries[0]) * he->nr_entries_allocated);
		hash_heads[h] = he;
	}

	callee |= (is_call << 63);
	for (i = 0; i < he->nr_entries; i++)
		if (he->entries[i] == callee)
			return;
	if (he->nr_entries == he->nr_entries_allocated) {
		unsigned long *t;
		he->nr_entries_allocated += 16;
		t = VG_(malloc)("hash_entry->entries2",
				sizeof(he->entries[0]) * he->nr_entries_allocated);
		VG_(memcpy)(t, he->entries, sizeof(he->entries[0]) * he->nr_entries);
		VG_(free)(he->entries);
		he->entries = t;
	}
	he->entries[he->nr_entries] = callee;
	he->nr_entries++;
}

static void
push_call_stack(unsigned long rip)
{
	struct rip_entry *caller = &thread_callstacks[VG_(get_running_tid)()];
	if (caller->nr_entries < NR_INLINE_RIPS) {
		caller->content[caller->nr_entries] = rip;
	} else {
		if (caller->nr_entries >= NR_INLINE_RIPS + caller->nr_entries_allocated) {
			caller->nr_entries_allocated += 32;
			caller->out_of_line_content = VG_(realloc)("rip_entry_out_of_line",
								   caller->out_of_line_content,
								   (caller->nr_entries_allocated - NR_INLINE_RIPS) * sizeof(caller->out_of_line_content[0]));
		}
		caller->out_of_line_content[caller->nr_entries - NR_INLINE_RIPS] = rip;
	}
	caller->nr_entries++;
	return;
}

static void
pop_call_stack(unsigned long to)
{
	struct rip_entry *caller = &thread_callstacks[VG_(get_running_tid)()];
	if (caller->nr_entries > 0) {
		unsigned long retaddr;
		if (caller->nr_entries - 1 >= NR_INLINE_RIPS)
			retaddr = caller->out_of_line_content[caller->nr_entries - NR_INLINE_RIPS - 1];
		else
			retaddr = caller->content[caller->nr_entries - 1];
		if (retaddr != to)
			VG_(printf)("Wanted to return to %lx!\n", retaddr);
		caller->nr_entries--;
	}
}

static void
bcg_post_clo_init(void)
{
}

static IRSB *
bcg_instrument(VgCallbackClosure* closure,
	       IRSB* bb,
	       VexGuestLayout* layout,
	       VexGuestExtents* vge,
	       IRType gWordTy,
	       IRType hWordTy)
{
	unsigned long rip = 0;
	unsigned long endRip;
	int i;

	if (bb->jumpkind != Ijk_Ret &&
	    bb->next->tag != Iex_Const) {
		IRTemp tmp;

		for (i = bb->stmts_used - 1; i >= 0; i--) {
			if (bb->stmts[i]->tag == Ist_IMark) {
				rip = bb->stmts[i]->Ist.IMark.addr;
				endRip = rip + bb->stmts[i]->Ist.IMark.len;
				break;
			}
		}
		tl_assert(i >= 0);
		if (bb->next->tag == Iex_RdTmp) {
			tmp = bb->next->Iex.RdTmp.tmp;
		} else {
			tmp = newIRTemp(bb->tyenv, Ity_I64);
			addStmtToIRSB(bb,
				      IRStmt_WrTmp(tmp, bb->next));
			bb->next = IRExpr_RdTmp(tmp);
		}
		addStmtToIRSB(bb,
			      IRStmt_Dirty(
				      unsafeIRDirty_0_N(
					      0,
					      "log_call",
					      log_call,
					      mkIRExprVec_3(
						      IRExpr_Const(IRConst_U64(rip)),
						      IRExpr_Const(IRConst_U64(bb->jumpkind == Ijk_Call)),
						      bb->next))));
	}

	if (bb->jumpkind == Ijk_Call) {
		IRTemp tmp;
		for (i = bb->stmts_used - 1; !rip && i >= 0; i--)
			if (bb->stmts[i]->tag == Ist_IMark) {
				rip = bb->stmts[i]->Ist.IMark.addr;
				endRip = rip + bb->stmts[i]->Ist.IMark.len;
			}
		if (bb->next->tag == Iex_RdTmp) {
			tmp = bb->next->Iex.RdTmp.tmp;
		} else {
			tmp = newIRTemp(bb->tyenv, Ity_I64);
			addStmtToIRSB(bb,
				      IRStmt_WrTmp(tmp, bb->next));
			bb->next = IRExpr_RdTmp(tmp);
		}
		addStmtToIRSB(bb,
			      IRStmt_Dirty(
				      unsafeIRDirty_0_N(
					      0,
					      "push_call_stack",
					      push_call_stack,
					      mkIRExprVec_1(
						      IRExpr_Const(IRConst_U64(endRip))))));
	}
	if (bb->jumpkind == Ijk_Ret) {
		IRTemp tmp;
		if (bb->next->tag == Iex_RdTmp) {
			tmp = bb->next->Iex.RdTmp.tmp;
		} else {
			tmp = newIRTemp(bb->tyenv, Ity_I64);
			addStmtToIRSB(bb,
				      IRStmt_WrTmp(tmp, bb->next));
			bb->next = IRExpr_RdTmp(tmp);
		}
		addStmtToIRSB(bb,
			      IRStmt_Dirty(
				      unsafeIRDirty_0_N(
					      0,
					      "pop_call_stack",
					      pop_call_stack,
					      mkIRExprVec_1(
						      IRExpr_RdTmp(tmp)
						      ))));
	}
	return bb;
}

static void
write_rip_entry(struct write_file *output, const struct rip_entry *re)
{
	int x;

	write_file(output, &re->rip, sizeof(re->rip));
	write_file(output, &re->nr_entries, sizeof(re->nr_entries));
	for (x = 0; x < re->nr_entries && x < NR_INLINE_RIPS; x++)
		write_file(output, &re->content[x], sizeof(re->content[x]));
	for ( ; x < re->nr_entries; x++)
		write_file(output, &re->out_of_line_content[x-NR_INLINE_RIPS], sizeof(re->out_of_line_content[0]));
}

static void
bcg_fini(Int exitcode)
{
	struct write_file output;
	Char buf[128];
	int x;
	struct hash_entry *he;

	x = 0;
	do {
		x++;
		VG_(sprintf)(buf, "callgraph%d.dat", x);
	} while (open_write_file(&output, buf) != 0);

	for (x = 0; x < NR_HASH_HEADS; x++) {
		for (he = hash_heads[x]; he; he = he->next) {
			write_rip_entry(&output, &he->rip);
			tl_assert(he->nr_entries > 0);
			write_file(&output, &he->nr_entries, sizeof(he->nr_entries));
			write_file(&output, he->entries, sizeof(he->entries[0]) * he->nr_entries);
		}
	}
	close_write_file(&output);
}

static void
bcg_pre_clo_init(void)
{
	VG_(details_name)("BCG");
	VG_(details_version)(NULL);
	VG_(details_description)("foo");
	VG_(details_copyright_author)("me");
	VG_(details_bug_reports_to)(VG_BUGS_TO);

	VG_(basic_tool_funcs)(bcg_post_clo_init, bcg_instrument, bcg_fini);
}

VG_DETERMINE_INTERFACE_VERSION(bcg_pre_clo_init)
