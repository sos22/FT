#include <err.h>
#include <stdio.h>
#include <stdlib.h>

struct rip_entry {
	unsigned long rip;
	unsigned long nr_items;
	unsigned long content[0];
};

static struct rip_entry *
read_rip_entry(FILE *f)
{
	unsigned long rip;
	unsigned nr_items;
	struct rip_entry *work;

	if (fread(&rip, sizeof(rip), 1, f) == 0)
		return NULL;
	if (fread(&nr_items, sizeof(nr_items), 1, f) != 1)
		err(1, "input truncated");
	work = malloc(sizeof(*work) + nr_items * sizeof(work->content[0]));
	if (fread(work->content, sizeof(work->content[0]), nr_items, f) != nr_items)
		err(1, "input truncated");
	work->rip = rip;
	work->nr_items = nr_items;
	return work;
}

static void
print_rip_entry(const struct rip_entry *re)
{
	int i;
	printf("%lx@", re->rip);
	for (i = 0; i < re->nr_items; i++) {
		if (i != 0)
			printf(", ");
		printf("%lx", re->content[i]);
	}
}

int
main()
{
	struct rip_entry *re;
	unsigned nr_entries;
	unsigned long *content;
	int i;

	while (1) {
		re = read_rip_entry(stdin);
		if (!re)
			break;
		if (fread(&nr_entries, sizeof(nr_entries), 1, stdin) != 1)
			err(1, "input truncated");
		content = malloc(sizeof(content[0]) * nr_entries);
		if (fread(content, sizeof(content[0]), nr_entries, stdin) != nr_entries)
			err(1, "input truncated");
		print_rip_entry(re);
		printf(": ");
		for (i = 0; i < nr_entries; i++) {
			if (i != 0)
				printf(", ");
			printf("%lx", content[i]);
		}
		printf("\n");

		free(content);
		free(re);
	}
	if (!feof(stdin))
		err(1, "reading input");
	return 0;
}
