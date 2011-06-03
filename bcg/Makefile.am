include $(top_srcdir)/Makefile.tool.am

noinst_PROGRAMS =
noinst_PROGRAMS += bcg-amd64-linux

BCG_SOURCES_COMMON = bcg_main.c gfsilgfs

bcg_amd64_linux_SOURCES      = $(BCG_SOURCES_COMMON)
bcg_amd64_linux_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
bcg_amd64_linux_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX)
bcg_amd64_linux_DEPENDENCIES = $(COREGRIND_LIBS_AMD64_LINUX)
bcg_amd64_linux_LDADD        = $(TOOL_LDADD_AMD64_LINUX)
bcg_amd64_linux_LDFLAGS      = $(TOOL_LDFLAGS_AMD64_LINUX)
