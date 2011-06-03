#include <err.h>
#include <stdio.h>
#include <stdlib.h>

struct hdr {
	int nr_loads;
	int nr_stores;
};

int
main()
{
	unsigned long *loads, *stores;
	struct hdr hdr;
	int i;

	while (1) {
		if (fread(&hdr, sizeof(hdr), 1, stdin) != 1)
			err(1, "reading header");

		printf("Loads: ");
		loads = calloc(sizeof(loads[0]), hdr.nr_loads);
		fread(loads, sizeof(loads[0]), hdr.nr_loads, stdin);
		for (i = 0; i < hdr.nr_loads; i++)
			printf("0x%lx ", loads[i]);
		free(loads);

		printf("\nStores: ");
		stores = calloc(sizeof(stores[0]), hdr.nr_stores);
		fread(stores, sizeof(stores[0]), hdr.nr_stores, stdin);
		for (i = 0; i < hdr.nr_stores; i++)
			printf("0x%lx ", stores[i]);
		free(stores);

		printf("\n");
	}
}
