#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

#include "../ft/shared.c"

struct address_set {
	int nr_entries;
	int nr_entries_allocated; /* including entry0.  Only valid if nr_entries >= 3 */
	/* Common case is for there to be <=2 entries in the set, so optimise for that. */
	unsigned long entry0;
	union {
		unsigned long entry1;
		unsigned long *entry1N;
	} u;
};

struct addr_hash_entry {
	struct addr_hash_entry *next;
	unsigned long addr;
	struct address_set stores;
};

#define NR_ADDR_HASH_HEADS 8193
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
	cursor->stores.nr_entries = 0;
	addr_hash_heads[hash] = cursor;
	return cursor;
}

static void
add_address_to_set(struct address_set *set, unsigned long addr)
{
	unsigned long t;
	int low, high;

	tl_assert(addr != 0);
	if (set->nr_entries == 0) {
		set->entry0 = addr;
	} else if (set->nr_entries == 1) {
		if (addr < set->entry0) {
			set->u.entry1 = set->entry0;
			set->entry0 = addr;
		} else if (addr > set->entry0) {
			set->u.entry1 = addr;
		} else {
			return;
		}
	} else if (set->nr_entries == 2) {
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
	sanity_check_set(set);
}

static void
log_store(unsigned long rip, unsigned long addr, unsigned size)
{
	struct addr_hash_entry *ahe = find_addr_hash_entry(addr);
	add_address_to_set(&ahe->stores, rip);
}

static void
do_store(unsigned long addr, unsigned long data, unsigned long size,
	 unsigned long rsp, unsigned long rip)
{
	if (addr < rsp - 128 || addr >= rsp + 8192)
		log_store(rip, addr, size);
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
	b = log_stores(bb);
	return b;
}

static void
ft2_fini(Int exitcode)
{
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
}

VG_DETERMINE_INTERFACE_VERSION(ft2_pre_clo_init)
