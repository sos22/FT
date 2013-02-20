#include <err.h>
#include <stdio.h>
#include <stdlib.h>

struct hdr {
	int nr_loads;
	int nr_stores;
};

struct rip_entry {
	unsigned long nr_items;
	unsigned long content[0];
};

static struct rip_entry *
read_rip_entry(FILE *f, int new_format)
{
	if (!new_format) {
		unsigned nr_items;
		struct rip_entry *work;

		if (fread(&nr_items, sizeof(nr_items), 1, f) != 1)
			err(1, "input truncated");
		work = malloc(sizeof(*work) + nr_items * sizeof(work->content[0]));
		if (fread(work->content, sizeof(work->content[0]), nr_items, f) != nr_items)
			err(1, "input truncated");
		work->nr_items = nr_items;
		return work;
	} else {
		unsigned long word;
		struct rip_entry *work;
		if (fread(&word, sizeof(word), 1, f) != 1) {
			err(1, "input truncated");
		}
		work = malloc(sizeof(*work) + sizeof(word));
		work->nr_items = 1;
		work->content[0] = word;
		return work;
	}
}

static void
print_rip_entry(const struct rip_entry *re)
{
	int i;
	printf("(");
	for (i = 0; i < re->nr_items; i++) {
		if (i != 0)
			printf(",");
		printf("%lx", re->content[i]);
	}
	printf(")");
}

int
main()
{
	struct rip_entry *re;
	struct hdr hdr;
	int i;
	unsigned long magic;
	int new_format;

	fread(&magic, sizeof(magic), 1, stdin);
	new_format = magic == 0x1122334455;
	if (new_format) {
		printf("New format\n");
	} else {
		printf("Old format\n");
		fseeko(stdin, 0, SEEK_SET);
	}
	while (1) {
		if (fread(&hdr, sizeof(hdr), 1, stdin) != 1)
			err(1, "reading header");

		re = read_rip_entry(stdin, new_format);
		print_rip_entry(re);
		free(re);
		printf(": Loads = {");
		for (i = 0; i < hdr.nr_loads; i++) {
			if (i != 0)
				printf("; ");
			re = read_rip_entry(stdin, new_format);
			print_rip_entry(re);
			free(re);
		}

		printf("}, Stores = {");
		for (i = 0; i < hdr.nr_stores; i++) {
			if (i != 0)
				printf("; ");
			re = read_rip_entry(stdin, new_format);
			print_rip_entry(re);
			free(re);
		}
		printf("}\n");
	}
}
