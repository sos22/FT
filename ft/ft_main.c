/* Based on nullgrind */
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_stacktrace.h"

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

static void *
my_malloc(ThreadId tid, SizeT n)
{
	StackTrace stack[2];
	UInt nr;
	UInt r;

	VG_(printf)("malloc %lx: ", n);
	nr = VG_(get_StackTrace)(tid, stack, sizeof(stack)/sizeof(stack[0]),
				 NULL, NULL, 0);
	for (r = 0; r < nr; r++)
		VG_(printf)("%llx ", stack[r]);
	VG_(printf)("\n");
	return VG_(cli_malloc)(8, n);
}

static void
my_free(ThreadId tid, void *p)
{
	VG_(cli_free)(p);
}

static void *
my_memalign(ThreadId tid, SizeT align, SizeT n)
{
	return VG_(cli_malloc)(align, n);
}

static void *
my_calloc(ThreadId tid, SizeT nmemb, SizeT size1)
{
	void *buf = VG_(cli_malloc)(8, nmemb * size1);
	VG_(memset)(buf, 0, nmemb * size1);
	return buf;
}

static void *
my_realloc(ThreadId tid, void *p, SizeT new_size)
{
	return VG_(cli_realloc)(p, new_size);
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
