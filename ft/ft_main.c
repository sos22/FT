/* Based on nullgrind */
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_stacktrace.h"

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
struct store_hash_entry {
	struct store_hash_entry *next;
	unsigned long rips;
	struct type_tag tag1; /* The common case is that each store
				 writes precisely one tag, so keep one
				 tag inline. */
	int nr_tags; /* This is zero if we should backtrack another
			level up the call stack. */
	struct type_tag *out_of_line_tags;
};

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

static
IRSB* nl_instrument ( VgCallbackClosure* closure,
                      IRSB* bb,
                      VexGuestLayout* layout, 
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{
	return bb;
}

static void nl_fini(Int exitcode)
{
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
                                 nl_instrument,
                                 nl_fini);

   VG_(printf)("Wibble.\n");
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
