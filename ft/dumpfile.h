struct type_tag {
	unsigned long allocation_rip;
	long allocation_size;
	unsigned offset;
};

struct range { /* Indicates that this store can write to a range of
		  bytes in a structure. */
	struct type_tag t;
	unsigned end;
};

struct table_site_header {
	unsigned long rip;
	unsigned nr_ranges;
};
