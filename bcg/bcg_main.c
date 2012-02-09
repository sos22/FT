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
#include "../ft/rips.c"

struct hash_entry {
	struct hash_entry *next;
	struct rip_entry rip;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long *entries;
};
#define NR_HASH_HEADS 65537
static struct hash_entry *hash_heads[NR_HASH_HEADS];

static unsigned
hash_fn(const struct rip_entry *caller, unsigned long rip)
{
	unsigned long val = hash_rip(caller, rip);
	while (val > NR_HASH_HEADS)
		val = (val % NR_HASH_HEADS) ^ (val / NR_HASH_HEADS);
	return val;
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

	maintain_call_stack(bb);

	return bb;
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
