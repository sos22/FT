#include <sys/types.h>

#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcfile.h"

#include "ft.h"

int
open_read_file(struct read_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(fname, VKI_O_RDONLY, 0);
	if (sr.isError)
		return sr.err;
	out->fd = sr.res;
	out->buf_cons = 0;
	out->buf_prod = 0;
	return 0;
}

int
read_file(struct read_file *rf, void *buf, size_t sz)
{
	unsigned to_copy;
	Int x;

	if (sz == 0)
		return 1;
	while (1) {
		to_copy = sz;
		if (rf->buf_prod > rf->buf_cons) {
			if (rf->buf_prod - rf->buf_cons < sz)
				to_copy = rf->buf_prod - rf->buf_cons;
			VG_(memcpy)(buf, rf->buf + rf->buf_cons, to_copy);
			rf->buf_cons += to_copy;
			sz -= to_copy;
			buf = (void *)((unsigned long)buf + to_copy);
			if (!sz)
				return 1;
		}
		tl_assert(rf->buf_prod == rf->buf_cons);
		rf->buf_cons = rf->buf_prod = 0;
		x = VG_(read)(rf->fd, rf->buf + rf->buf_prod, sizeof(rf->buf) - rf->buf_prod);
		if (x == 0)
			return 0;
		tl_assert(x > 0);
		rf->buf_prod += x;
	}
}

void
close_read_file(struct read_file *rf)
{
	VG_(close)(rf->fd);
}

int
open_write_file(struct write_file *out, const Char *fname)
{
	SysRes sr;

	sr = VG_(open)(fname, VKI_O_WRONLY|VKI_O_CREAT|VKI_O_TRUNC, 0600);
	if (sr.isError)
		return sr.err;
	out->fd = sr.res;
	out->buf_prod = 0;
	return 0;
}

void
write_file(struct write_file *wf, const void *buf, size_t sz)
{
	unsigned to_copy;
	unsigned x;
	int y;

	while (sz != 0) {
		if (wf->buf_prod == sizeof(wf->buf)) {
			for (x = 0; x < wf->buf_prod; x += y) {
				y = VG_(write)(wf->fd, wf->buf + x, wf->buf_prod - x);
				tl_assert(y > 0);
			}
			wf->buf_prod = 0;
		}

		to_copy = sz;
		if (wf->buf_prod + to_copy >= sizeof(wf->buf))
			to_copy = sizeof(wf->buf) - wf->buf_prod;
		VG_(memcpy)(wf->buf + wf->buf_prod, buf, to_copy);
		wf->buf_prod += to_copy;
		buf = (void *)((unsigned long)buf + to_copy);
		sz -= to_copy;
	}
}

void
close_write_file(struct write_file *wf)
{
	int x, y;
	for (x = 0; x < wf->buf_prod; x+= y) {
		y = VG_(write)(wf->fd, wf->buf + x, wf->buf_prod - x);
		tl_assert(y > 0);
	}
	VG_(close)(wf->fd);
}
