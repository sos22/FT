#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include "dumpfile.h"

int
main()
{
	struct table_site_header tsh;
	struct range *tags;
	int x;

	while (!feof(stdin)) {
		if (fread(&tsh, sizeof(tsh), 1, stdin) != 1) {
			if (ferror(stdin))
				err(1, "reading input");
			continue;
		}
		tags = calloc(sizeof(tags[0]), tsh.nr_ranges);
		if (!tags)
			err(1, "allocating space for %d tags", tsh.nr_ranges);
		if (fread(tags, sizeof(tags[0]), tsh.nr_ranges, stdin) != tsh.nr_ranges)
			errx(1, "input truncated?");
		printf("%16lx %d ", tsh.rip, tsh.nr_ranges);
		for (x = 0; x < tsh.nr_ranges; x++) {
			printf("%lx:%lx:%x:%x\t",
			       tags[x].t.allocation_rip,
			       tags[x].t.allocation_size,
			       tags[x].t.offset,
			       tags[x].end);
		}
		printf("\n");
		free(tags);
	}
	return 0;
}
