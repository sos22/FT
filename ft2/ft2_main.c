#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_threadstate.h"

#include "libvex_guest_offsets.h"

#include "../ft/shared.c"

static void
do_store(unsigned long addr, unsigned long data, unsigned long size,
	 unsigned long rsp, unsigned long rip)
{
	VG_(memcpy)( (void *)addr, &data, size);
}

static void
do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
	  unsigned long rsp, unsigned long rip)
{
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
	return log_call_return(log_stores(bb));
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
