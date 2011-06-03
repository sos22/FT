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

struct hash_entry {
	struct hash_entry *next;
	unsigned long rip;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long *entries;
};
#define NR_HASH_HEADS 65537
static struct hash_entry *hash_heads[NR_HASH_HEADS];

static unsigned
hash_address(unsigned long addr)
{
	while (addr > NR_HASH_HEADS)
		addr = (addr % NR_HASH_HEADS) ^ (addr / NR_HASH_HEADS);
	return addr;
}

static void
log_call(unsigned long caller, unsigned long callee)
{
	unsigned h = hash_address(caller);
	struct hash_entry *he;
	unsigned i;

	for (he = hash_heads[h]; he && he->rip != caller; he = he->next)
		;
	if (!he) {
		he = VG_(malloc)("hash_entry", sizeof(*he));
		he->next = hash_heads[h];
		he->rip = caller;
		he->nr_entries = 0;
		he->nr_entries_allocated = 4;
		he->entries = VG_(malloc)("hash_entry->entries",
					  sizeof(he->entries[0]) * he->nr_entries_allocated);
		hash_heads[h] = he;
	}

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
	if (bb->jumpkind == Ijk_Call &&
	    bb->next->tag != Iex_Const) {
		IRTemp tmp;
		unsigned long rip;
		int i;

		for (i = bb->stmts_used - 1; i >= 0; i--) {
			if (bb->stmts[i]->tag == Ist_IMark) {
				rip = bb->stmts[i]->Ist.IMark.addr;
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
					      mkIRExprVec_2(
						      IRExpr_Const(IRConst_U64(rip)),
						      bb->next))));
	}
	return bb;
}

struct header {
	unsigned long rip;
	unsigned long nr_entries;
};

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
			struct header hdr;
			hdr.rip = he->rip;
			hdr.nr_entries = he->nr_entries;
			tl_assert(he->nr_entries > 0);
			write_file(&output, &hdr, sizeof(hdr));
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
