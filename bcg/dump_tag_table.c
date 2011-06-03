#include <err.h>
#include <stdio.h>
#include <stdlib.h>

struct header {
	unsigned long rip;
	unsigned long nr_entries;
};

int
main()
{
	struct header hdr;
	unsigned long *content;
	int i;

	while (1) {
		if (!fread(&hdr, 1, sizeof(hdr), stdin))
			break;
		content = malloc(sizeof(content[0]) * hdr.nr_entries);
		if (fread(content, sizeof(content[0]), hdr.nr_entries, stdin) != hdr.nr_entries)
			err(1, "input truncated");
		printf("%lx: ", hdr.rip);
		for (i = 0; i < hdr.nr_entries; i++) {
			if (i != 0)
				printf(", ");
			printf("%lx", content[i]);
		}
		printf("\n");
		free(content);
	}
	if (!feof(stdin))
		err(1, "reading input");
	return 0;
}
