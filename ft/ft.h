struct read_file {
	int fd;
	unsigned buf_cons;
	unsigned buf_prod;
	unsigned char buf[128];
};

int open_read_file(struct read_file *out, const Char *fname);
int read_file(struct read_file *rf, void *buf, size_t sz);
void close_read_file(struct read_file *rf);

struct write_file {
	int fd;
	unsigned buf_prod;
	unsigned char buf[1024];
};

int open_write_file(struct write_file *out, const Char *fname);
void write_file(struct write_file *wf, const void *buf, size_t sz);
void close_write_file(struct write_file *wf);

