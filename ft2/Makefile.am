include $(top_srcdir)/Makefile.tool.am

noinst_PROGRAMS =
noinst_PROGRAMS += ft2-amd64-linux vgpreload_ft2-amd64-linux.so

FT2_SOURCES_COMMON = ft2_main.c

ft2_amd64_linux_SOURCES      = $(FT2_SOURCES_COMMON)
ft2_amd64_linux_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
ft2_amd64_linux_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX)
ft2_amd64_linux_DEPENDENCIES = $(COREGRIND_LIBS_AMD64_LINUX)
ft2_amd64_linux_LDADD        = $(TOOL_LDADD_AMD64_LINUX)
ft2_amd64_linux_LDFLAGS      = $(TOOL_LDFLAGS_AMD64_LINUX)

vgpreload_ft2_amd64_linux_so_SOURCES      =
vgpreload_ft2_amd64_linux_so_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
vgpreload_ft2_amd64_linux_so_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX) $(AM_CFLAGS_PIC)
vgpreload_ft2_amd64_linux_so_DEPENDENCIES = $(LIBREPLACEMALLOC_AMD64_LINUX)
vgpreload_ft2_amd64_linux_so_LDFLAGS      = \
        $(PRELOAD_LDFLAGS_AMD64_LINUX) \
        $(LIBREPLACEMALLOC_LDFLAGS_AMD64_LINUX)
