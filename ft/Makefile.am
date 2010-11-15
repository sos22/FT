include $(top_srcdir)/Makefile.tool.am

noinst_PROGRAMS = 
noinst_PROGRAMS += ft-amd64-linux

FT_SOURCES_COMMON = ft_main.c

ft_amd64_linux_SOURCES      = $(FT_SOURCES_COMMON)
ft_amd64_linux_CPPFLAGS     = $(AM_CPPFLAGS_AMD64_LINUX)
ft_amd64_linux_CFLAGS       = $(AM_CFLAGS_AMD64_LINUX)
ft_amd64_linux_DEPENDENCIES = $(COREGRIND_LIBS_AMD64_LINUX)
ft_amd64_linux_LDADD        = $(TOOL_LDADD_AMD64_LINUX)
ft_amd64_linux_LDFLAGS      = $(TOOL_LDFLAGS_AMD64_LINUX)
