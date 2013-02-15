#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

#define logged_malloc(site, amount, owner) VG_(malloc)(site, amount)
#define logged_realloc(site, ptr, oldsize, newsize, owner) VG_(realloc)(site, ptr, newsize);
#define log_free(amt, owner) do{}while (0)

#include "../ft/io.c"

/* The hash table is pretty much a mapping from indirect call and
   branch instructions to the sets of instructions which they might
   target. */
struct hash_entry {
	struct hash_entry *next;
	/* This gets bitwise or'd into ->src if this is a call
	 * instruction */
#define HE_IS_CALL (1ul << 63)
	unsigned long src;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long *dest;
};
#define NR_HASH_HEADS 65537
static struct hash_entry *hash_heads[NR_HASH_HEADS];

static unsigned
hash_fn(unsigned long rip)
{
	unsigned long val = rip / 8;
	while (val >= NR_HASH_HEADS)
		val = (val % NR_HASH_HEADS) ^ (val / NR_HASH_HEADS);
	return val;
}

static void
log_call(unsigned long src, unsigned long is_call, unsigned long dest)
{
	unsigned h = hash_fn(src);
	struct hash_entry *he;
	unsigned i;

	if (is_call) {
		src |= HE_IS_CALL;
	}
	tl_assert(h < NR_HASH_HEADS);
	for (he = hash_heads[h]; he && src != he->src; he = he->next) {
		;
	}
	if (!he) {
		he = VG_(malloc)("hash_entry", sizeof(*he));
		he->next = hash_heads[h];
		he->src = src;
		he->nr_entries = 0;
		he->nr_entries_allocated = 7;
		he->dest = VG_(malloc)("hash_entry->entries",
				       sizeof(he->dest[0]) * he->nr_entries_allocated);
		hash_heads[h] = he;
	} else {
		for (i = 0; i < he->nr_entries; i++) {
			if (he->dest[i] == dest) {
				return;
			}
		}
		if (he->nr_entries == he->nr_entries_allocated) {
			unsigned long *t;
			he->nr_entries_allocated += 16;
			t = VG_(malloc)("hash_entry->entries2",
					sizeof(he->dest[0]) * he->nr_entries_allocated);
			VG_(memcpy)(t, he->dest, sizeof(he->dest[0]) * he->nr_entries);
			VG_(free)(he->dest);
			he->dest = t;
		}
	}
	he->dest[he->nr_entries] = dest;
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
	int i;

	if (bb->jumpkind != Ijk_Ret &&
	    bb->next->tag != Iex_Const) {
		IRTemp tmp;

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
					      mkIRExprVec_3(
						      IRExpr_Const(IRConst_U64(rip)),
						      IRExpr_Const(IRConst_U64(bb->jumpkind == Ijk_Call)),
						      bb->next))));
	}

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
			tl_assert(he->nr_entries > 0);
			write_file(&output, &he->src, sizeof(he->src));
			write_file(&output, &he->nr_entries, sizeof(he->nr_entries));
			write_file(&output, he->dest, sizeof(he->dest[0]) * he->nr_entries);
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
