#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

#include "../ft/shared.c"
#include "../ft/io.c"

struct address_set {
	int nr_entries;
	int nr_entries_allocated:31; /* including entry0.  Only valid if nr_entries >= 3 */
	unsigned int loud:1;
	/* Common case is for there to be <=2 entries in the set, so optimise for that. */
	unsigned long entry0;
	union {
		unsigned long entry1;
		unsigned long *entry1N;
	} u;
};

struct addr_set_pair {
	struct address_set stores;
	struct address_set loads;
};

struct addr_hash_entry {
	struct addr_hash_entry *next;
	unsigned long addr;
	struct addr_set_pair content;
};

#define NR_ADDR_HASH_HEADS 100271
static struct addr_hash_entry *
addr_hash_heads[NR_ADDR_HASH_HEADS];

static void
sanity_check_set(const struct address_set *as)
{
	int x;

	tl_assert(as->nr_entries >= 0);
	if (as->nr_entries <= 1)
		return;
	if (as->nr_entries == 2) {
		tl_assert(as->entry0 < as->u.entry1);
		return;
	}
	tl_assert(as->nr_entries <= as->nr_entries_allocated);
	tl_assert(as->entry0 < as->u.entry1N[0]);
	for (x = 0; x < as->nr_entries-2; x++)
		tl_assert(as->u.entry1N[x] < as->u.entry1N[x+1]);
}

static unsigned
hash_address(unsigned long addr)
{
	while (addr > NR_ADDR_HASH_HEADS)
		addr = (addr % NR_ADDR_HASH_HEADS) ^ (addr / NR_ADDR_HASH_HEADS);
	return addr;
}

static struct addr_hash_entry *
find_addr_hash_entry(unsigned long addr)
{
	unsigned hash = hash_address(addr / 8);
	struct addr_hash_entry *cursor;
	for (cursor = addr_hash_heads[hash]; cursor && cursor->addr != addr; cursor = cursor->next)
		;
	if (cursor) {
		return cursor;
	}
	cursor = VG_(malloc)("addr_hash_entry", sizeof(*cursor));
	cursor->next = addr_hash_heads[hash];
	cursor->addr = addr;
	cursor->content.stores.loud = 0;
	cursor->content.loads.loud = 0;
	cursor->content.stores.nr_entries = 0;
	cursor->content.loads.nr_entries = 0;
	addr_hash_heads[hash] = cursor;
	return cursor;
}

static void
add_address_to_set(struct address_set *set, unsigned long addr,
		   const char *sname, unsigned long on_behalf_of)
{
	unsigned long t;
	int low, high;
	int loud = set->loud;

	if (addr == 0x6060c7 || addr == 0x9a8266 || addr == 0x9a8259)
		set->loud = loud = 1;
	if (loud)
		VG_(printf)("Add address %lx to set %s(%p) on behalf of %lx\n",
			    addr, sname, set, on_behalf_of);
	tl_assert(addr != 0);
	if (set->nr_entries == 0) {
		if (loud)
			VG_(printf)("Fresh set\n");
		set->entry0 = addr;
	} else if (set->nr_entries == 1) {
		if (loud)
			VG_(printf)("Currently size 1 (%lx)\n",
				    set->entry0);
		if (addr < set->entry0) {
			set->u.entry1 = set->entry0;
			set->entry0 = addr;
		} else if (addr > set->entry0) {
			set->u.entry1 = addr;
		} else {
			return;
		}
	} else if (set->nr_entries == 2) {
		if (loud)
			VG_(printf)("Currently size 2 (%lx, %lx)\n",
				    set->entry0, set->u.entry1);
		t = set->u.entry1;
		if (addr == set->entry0 ||
		    addr == t)
			return;
		set->nr_entries_allocated = 16;
		set->u.entry1N = VG_(malloc)("address set OOL", sizeof(set->u.entry1N[0]) * (set->nr_entries_allocated-1));
		if (addr < set->entry0) {
			set->u.entry1N[0] = set->entry0;
			set->u.entry1N[1] = t;
			set->entry0 = addr;
		} else if (addr < t) {
			set->u.entry1N[0] = addr;
			set->u.entry1N[1] = t;
		} else {
			set->u.entry1N[0] = t;
			set->u.entry1N[1] = addr;
		}
	} else {
		if (loud)
			VG_(printf)("Currently size %d\n", set->nr_entries);
		if (addr == set->entry0)
			return;
		if (addr < set->entry0) {
			if (set->nr_entries_allocated == set->nr_entries) {
				set->nr_entries_allocated *= 4;
				set->u.entry1N = VG_(realloc)("address set OOL",
							      set->u.entry1N,
							      sizeof(set->u.entry1N[0]) * (set->nr_entries_allocated-1));
			}
			VG_(memmove)(set->u.entry1N + 1,
				     set->u.entry1N,
				     sizeof(set->u.entry1N[0]) *
				     (set->nr_entries - 1));
			set->u.entry1N[0] = set->entry0;
			set->entry0 = addr;
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
				if (addr < set->u.entry1N[probe]) {
					tl_assert(high != probe);
					high = probe;
				} else if (addr == set->u.entry1N[probe]) {
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
				set->u.entry1N = VG_(realloc)("address set OOL",
							      set->u.entry1N,
							      sizeof(set->u.entry1N[0]) * (set->nr_entries_allocated-1));
			}
			VG_(memmove)(set->u.entry1N + low + 1,
				     set->u.entry1N + low,
				     sizeof(set->u.entry1N[0]) * (set->nr_entries - 1 - low));
			set->u.entry1N[low] = addr;
		}
	}
	set->nr_entries++;
	//sanity_check_set(set);
}

static void
log_store(unsigned long rip, unsigned long addr, unsigned size)
{
	struct addr_hash_entry *ahe = find_addr_hash_entry(addr);
	add_address_to_set(&ahe->content.stores, rip, "store", addr);
}

static void
do_store(unsigned long addr, unsigned long data, unsigned long size,
	 unsigned long rsp, unsigned long rip)
{
	if (addr < rsp - 128 || addr >= rsp + 8192)
		log_store(rip, addr, size);
	if (addr == 0xe2fba0)
		VG_(printf)("store %lx -> %lx from %lx\n", data, addr, rip);
	VG_(memcpy)( (void *)addr, &data, size);
}

static void
do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
	  unsigned long rsp, unsigned long rip)
{
	if (addr < rsp - 128 || addr >= rsp + 8192)
		log_store(rip, addr, 16);
	((unsigned long *)addr)[0] = x1;
	((unsigned long *)addr)[1] = x2;
	if (addr == 0xe2fba0)
		VG_(printf)("store2 %lx from %lx\n", addr, rip);
}

static void
do_log_load(unsigned long addr, unsigned long rip, unsigned long rsp)
{
	struct addr_hash_entry *ahe;
	if (addr >= rsp - 128 && addr <= rsp + 8192)
		return;
	if (addr == 0xe2fba0)
		VG_(printf)("Load %lx from %lx\n", addr, rip);
	ahe = find_addr_hash_entry(addr);
	add_address_to_set(&ahe->content.loads, rip, "load", addr);
}

static void
log_this_load(IRSB *irsb, IRExpr *addr, unsigned long rip)
{
	IRTemp rsp;
	if (addr->tag != Iex_RdTmp) {
		IRTemp t = newIRTemp(irsb->tyenv, Ity_I64);
		addStmtToIRSB(irsb,
			      IRStmt_WrTmp(t, addr));
		addr = IRExpr_RdTmp(t);
	}
	rsp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(rsp, IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
	add_dirty_call(irsb, "log_load", do_log_load, addr,
		       IRExpr_Const(IRConst_U64(rip)),
		       IRExpr_RdTmp(rsp),
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

static IRSB *
log_loads(IRSB *inp)
{
	IRSB *out = deepCopyIRSBExceptStmts(inp);
	int x;
	IRStmt *stmt;
	unsigned long instr_start;

	instr_start = 0xdeadbabebeefface;
	for (x = 0; x < inp->stmts_used; x++) {
		stmt = inp->stmts[x];
		switch (stmt->tag) {
		case Ist_IMark:
			instr_start = stmt->Ist.IMark.addr;
			break;
		case Ist_Put:
			log_loads_expr(out, stmt->Ist.Put.data, instr_start);
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
}

static IRSB *
ft2_instrument(VgCallbackClosure* closure,
	       IRSB* bb,
	       VexGuestLayout* layout,
	       VexGuestExtents* vge,
	       IRType gWordTy,
	       IRType hWordTy)
{
	IRSB *b;
	b = log_loads(log_stores(bb));
	return b;
}

struct set_of_sets_entry {
	struct set_of_sets_entry *next;
	unsigned long h;
	struct addr_set_pair content;
};

#define NR_SS_HEADS 32768
static struct set_of_sets_entry *
ss_heads[NR_SS_HEADS];

static unsigned long
hash_address_set(const struct address_set *s)
{
	unsigned long hash;
	int x;

	switch (s->nr_entries) {
	case 0:
		return 0;
	case 1:
		return s->entry0;
	case 2:
		return s->entry0 * 4099 + s->u.entry1;
	default:
		hash = s->entry0;
		for (x = 1; x < s->nr_entries; x++)
			hash = hash * 8191 + s->u.entry1N[x-1];
		return hash;
	}
}

static unsigned long
hash_addr_set_pair(const struct addr_set_pair *s)
{
	return hash_address_set(&s->loads) * 17 +
		hash_address_set(&s->stores);
}

static int
sets_equal(const struct address_set *s1, const struct address_set *s2)
{
	int x;

	if (s1->nr_entries != s2->nr_entries)
		return 0;
	if (s1->nr_entries == 0)
		return 1;
	if (s1->entry0 != s2->entry0)
		return 0;
	if (s1->nr_entries == 1)
		return 1;
	if (s1->nr_entries == 2)
		return s1->u.entry1 == s2->u.entry1;
	for (x = 0; x < s1->nr_entries - 1; x++)
		if (s1->u.entry1N[x] != s2->u.entry1N[x])
			return 0;
	return 1;
}

static int
set_pairs_equal(const struct addr_set_pair *a, const struct addr_set_pair *b)
{
	return sets_equal(&a->stores, &b->stores) &&
		sets_equal(&a->loads, &b->loads);
}

static void
dump_set(const struct address_set *as)
{
	int i;
	switch (as->nr_entries) {
	case 0:
		VG_(printf)("\t\t<empty>\n");
		break;
	case 1:
		VG_(printf)("\t\t0x%lx\n", as->entry0);
		break;
	case 2:
		VG_(printf)("\t\t0x%lx\n", as->entry0);
		VG_(printf)("\t\t0x%lx\n", as->u.entry1);
		break;
	default:
		VG_(printf)("\t\t0x%lx\n", as->entry0);
		for (i = 0; i < as->nr_entries - 1; i++)
			VG_(printf)("\t\t0x%lx\n", as->u.entry1N[i]);
		break;
	}
}

static void
dump_set_pair(const struct addr_set_pair *s)
{
	VG_(printf)("\tStores:\n");
	dump_set(&s->stores);
	VG_(printf)("\tLoads:\n");
	dump_set(&s->loads);
}

/* Add the set @s to the global set of sets.  Zap it to an empty set
   at the same time. */
static void
fold_set_to_global_set(struct addr_set_pair *s)
{
	unsigned long h = hash_addr_set_pair(s);
	unsigned head = h % NR_SS_HEADS;
	struct set_of_sets_entry *sse;
	int loud = s->stores.loud | s->loads.loud;

	if (loud) {
		VG_(printf)("Folding %p to global:\n", s);
		dump_set_pair(s);
	}

	for (sse = ss_heads[head]; sse; sse = sse->next) {
		if (sse->h == h &&
		    set_pairs_equal(s, &sse->content)) {
			if (loud)
				VG_(printf)("Suppress duplicate\n");
			if (s->stores.nr_entries > 2)
				VG_(free)(s->stores.u.entry1N);
			s->stores.nr_entries = 0;
			s->stores.nr_entries_allocated = 0;

			if (s->loads.nr_entries > 2)
				VG_(free)(s->loads.u.entry1N);
			s->loads.nr_entries = 0;
			s->loads.nr_entries_allocated = 0;
			return;
		}
	}

	sse = VG_(malloc)("set_of_sets_entry", sizeof(*sse));
	sse->h = h;
	sse->content = *s;
	s->stores.nr_entries = 0;
	s->stores.nr_entries_allocated = 0;
	s->loads.nr_entries = 0;
	s->loads.nr_entries_allocated = 0;
	sse->next = ss_heads[head];
	ss_heads[head] = sse;
}
struct hdr {
	int nr_loads;
	int nr_stores;
};

static void
ft2_fini(Int exitcode)
{
	int x;
	struct addr_hash_entry *ahe;
	struct set_of_sets_entry *sse;
	struct write_file output;
	Char buf[128];

	for (x = 0; x < NR_ADDR_HASH_HEADS; x++)
		for (ahe = addr_hash_heads[x]; ahe; ahe = ahe->next)
			fold_set_to_global_set(&ahe->content);

	x = 0;
	do {
		x++;
		VG_(sprintf)(buf, "types%d.dat", x);
	} while (open_write_file(&output, buf) != 0);

	for (x = 0; x < NR_SS_HEADS; x++) {
		for (sse = ss_heads[x]; sse; sse = sse->next) {
			int loud = sse->content.stores.loud | sse->content.loads.loud;
			if (loud)
				VG_(printf)("Writing loud SSE with %d stores and %d loads at %lx\n",
					    sse->content.stores.nr_entries,
					    sse->content.loads.nr_entries,
					    output.offset);
			if (sse->content.stores.nr_entries > 0 ||
			    sse->content.loads.nr_entries > 0) {
				struct hdr hdr;
				hdr.nr_loads = sse->content.loads.nr_entries;
				hdr.nr_stores = sse->content.stores.nr_entries;
				write_file(&output, &hdr, sizeof(hdr));
				if (sse->content.loads.nr_entries > 0) {
					write_file(&output, &sse->content.loads.entry0,
						   sizeof(sse->content.loads.entry0));
					if (sse->content.loads.nr_entries == 2) {
						write_file(&output, &sse->content.loads.u.entry1,
							   sizeof(sse->content.loads.u.entry1));
					} else {
						write_file(&output, sse->content.loads.u.entry1N,
							   sizeof(sse->content.loads.u.entry1N[0]) *
							   (sse->content.loads.nr_entries-1));
					}
				}
				if (sse->content.stores.nr_entries > 0) {
					write_file(&output, &sse->content.stores.entry0,
						   sizeof(sse->content.stores.entry0));
					if (sse->content.stores.nr_entries == 2) {
						write_file(&output, &sse->content.stores.u.entry1,
							   sizeof(sse->content.stores.u.entry1));
					} else {
						write_file(&output, sse->content.stores.u.entry1N,
							   sizeof(sse->content.stores.u.entry1N[0]) *
							   (sse->content.stores.nr_entries-1));
					}
				}
			}
		}
	}
	VG_(printf)("Total file size %lx\n", output.offset);
	close_write_file(&output);
}

static void
refresh_tags(void *base, unsigned long size)
{
	unsigned long start = (unsigned long)base & ~7ul;
	unsigned long end = ((unsigned long)base + size + 7) & ~7ul;
	unsigned long ptr;
	struct addr_hash_entry *ahe;
	int x;

	if (size >= NR_ADDR_HASH_HEADS * 16) {
		for (x = 0; x < NR_ADDR_HASH_HEADS; x++) {
			for (ahe = addr_hash_heads[x]; ahe; ahe = ahe->next) {
				if (ahe->addr >= start && ahe->addr < end)
					fold_set_to_global_set(&ahe->content);
			}
		}
	} else {
		for (ptr = start; ptr < end; ptr += 8) {
			ahe = find_addr_hash_entry(ptr);
			if (ahe)
				fold_set_to_global_set(&ahe->content);
		}
	}
}

static void
ft2_free(ThreadId tid, void *p)
{
	VG_(cli_free)(p);
}

static void *
ft2_memalign(ThreadId tid, SizeT align, SizeT n)
{
	void *res;
	if (align < 8)
		align = 8;
	n = (n + 7ul) & ~7ul;

	res = VG_(cli_malloc)(align, n);
	if (res)
		refresh_tags(res, n);
	return res;
}

static void *
ft2_malloc(ThreadId tid, SizeT n)
{
	return ft2_memalign(tid, 0, n);
}

static void *
ft2_calloc(ThreadId tid, SizeT nmemb, SizeT size1)
{
	void *buf = ft2_malloc(tid, nmemb * size1);
	if (buf) {
		VG_(memset)(buf, 0, nmemb * size1);
		refresh_tags(buf, nmemb * size1);
	}
	return buf;
}

static void *
ft2_realloc(ThreadId tid, void *p, SizeT new_size)
{
	void *n;
	if (new_size == 0) {
		ft2_free(tid, p);
		return NULL;
	}
	if (p == NULL)
		return ft2_malloc(tid, new_size);
	n = VG_(cli_realloc)(p, new_size);
	if (n != 0)
		refresh_tags(n, new_size);
	return n;
}

static void
ft2_pre_clo_init(void)
{
	VG_(details_name)("FT2");
	VG_(details_version)(NULL);
	VG_(details_description)("foo");
	VG_(details_copyright_author)("me");
	VG_(details_bug_reports_to)(VG_BUGS_TO);

	VG_(basic_tool_funcs)(ft2_post_clo_init, ft2_instrument, ft2_fini);

	VG_(needs_malloc_replacement)(ft2_malloc,
				      ft2_malloc,
				      ft2_malloc,
				      ft2_memalign,
				      ft2_calloc,
				      ft2_free,
				      ft2_free,
				      ft2_free,
				      ft2_realloc,
				      0);
}

VG_DETERMINE_INTERFACE_VERSION(ft2_pre_clo_init)
