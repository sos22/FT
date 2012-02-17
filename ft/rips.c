#define NR_INLINE_RIPS 8

struct rip_entry {
	unsigned long rip;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long content[NR_INLINE_RIPS];
	unsigned long *out_of_line_content;
};

static struct rip_entry thread_callstacks[VG_N_THREADS];

static unsigned long
get_re_entry(const struct rip_entry *re, unsigned idx)
{
	if (idx >= NR_INLINE_RIPS)
		return re->out_of_line_content[idx-NR_INLINE_RIPS];
	else
		return re->content[idx];
}

/* advance to the next one in a way which avoids considering any
   cycles in the stack (e.g. recursive functions). */
static int
next_re_idx(const struct rip_entry *re, unsigned long entry)
{
	unsigned long entry2;
	int y;

	for (y = 0; y < re->nr_entries; y++) {
		entry2 = get_re_entry(re, y);
		if (entry2 == entry)
			return y - 1;
	}
	tl_assert(0);
	return -1;
}

static unsigned
hash_rip(const struct rip_entry *re, unsigned long rip)
{
	unsigned long addr = rip;
	unsigned long entry;
	int x;
	int nr_inline = re->nr_entries;
	if (nr_inline > NR_INLINE_RIPS)
		nr_inline = NR_INLINE_RIPS;
	for (x = re->nr_entries - 1; x >= 0; ) {
		entry = get_re_entry(re, x);
		addr = ((addr << 31) | (addr >> 33)) ^ entry;
		x = next_re_idx(re, entry);
	}
	return addr;
}

static int
rips_equal(const struct rip_entry *re1, const struct rip_entry *re2, unsigned long rip)
{
	int idx1, idx2;
	unsigned long entry1, entry2;

	if (re1->rip != rip)
		return 0;
	idx1 = re1->nr_entries - 1;
	idx2 = re2->nr_entries - 1;
	while (idx1 >= 0 && idx2 >= 0) {
		entry1 = get_re_entry(re1, idx1);
		entry2 = get_re_entry(re2, idx2);
		if (entry1 != entry2)
			return 0;
		idx1 = next_re_idx(re1, entry1);
		idx2 = next_re_idx(re2, entry2);
	}
	if (idx1 >= 0 || idx2 >= 0)
		return 0;
	return 1;
}

static void
copy_rip_entry(struct rip_entry *dest, const struct rip_entry *src, unsigned long rip)
{
	int nr_inline;

	dest->nr_entries = src->nr_entries;
	if (dest->nr_entries < NR_INLINE_RIPS) {
		dest->nr_entries_allocated = 0;
		nr_inline = dest->nr_entries;
	} else {
		dest->nr_entries_allocated = dest->nr_entries - NR_INLINE_RIPS;
		nr_inline = NR_INLINE_RIPS;
	}
	VG_(memcpy)(dest->content, src->content, sizeof(dest->content[0]) * nr_inline);
	if (dest->nr_entries_allocated != 0) {
		dest->out_of_line_content = logged_malloc("rip_entry_content",
							  sizeof(dest->content[0]) * dest->nr_entries_allocated,
							  mallocer_rip_entry_content);
		VG_(memcpy)(dest->out_of_line_content, src->out_of_line_content,
			    sizeof(dest->out_of_line_content[0]) * dest->nr_entries_allocated);
	} else {
		/* For sanity */
		dest->out_of_line_content = NULL;
	}
	dest->rip = rip;
}

static void
print_rip_entry(const struct rip_entry *re)
{
	int i;
	VG_(printf)("%lx: ", re->rip);
	for (i = 0; i < re->nr_entries; i++) {
		if (i != 0)
			VG_(printf)(", ");
		VG_(printf)("%lx", get_re_entry(re, i));
	}
	VG_(printf)("\n");
}

static void
push_call_stack(unsigned long rip)
{
	struct rip_entry *caller = &thread_callstacks[VG_(get_running_tid)()];
	if (caller->nr_entries < NR_INLINE_RIPS) {
		caller->content[caller->nr_entries] = rip;
	} else {
		if (caller->nr_entries >= NR_INLINE_RIPS + caller->nr_entries_allocated) {
			caller->nr_entries_allocated += 32;
			caller->out_of_line_content =
				logged_realloc("rip_entry_out_of_line",
					       caller->out_of_line_content,
					       (caller->nr_entries_allocated - 32) * sizeof(caller->out_of_line_content[0]),
					       caller->nr_entries_allocated * sizeof(caller->out_of_line_content[0]),
					       mallocer_rip_entry_content);
		}
		tl_assert(caller->nr_entries - NR_INLINE_RIPS < caller->nr_entries_allocated);
		caller->out_of_line_content[caller->nr_entries - NR_INLINE_RIPS] = rip;
	}
	caller->nr_entries++;
	return;
}

static void
pop_call_stack(unsigned long to)
{
	struct rip_entry *caller = &thread_callstacks[VG_(get_running_tid)()];
	if (caller->nr_entries > 0) {
		unsigned long retaddr;
		if (caller->nr_entries - 1 >= NR_INLINE_RIPS)
			retaddr = caller->out_of_line_content[caller->nr_entries - NR_INLINE_RIPS - 1];
		else
			retaddr = caller->content[caller->nr_entries - 1];
		if (retaddr != to)
			VG_(printf)("Wanted to return to %lx!\n", retaddr);
		caller->nr_entries--;
	}
}

static void
write_rip_entry(struct write_file *output, const struct rip_entry *re)
{
	int x;

	write_file(output, &re->rip, sizeof(re->rip));
	write_file(output, &re->nr_entries, sizeof(re->nr_entries));
	for (x = 0; x < re->nr_entries && x < NR_INLINE_RIPS; x++)
		write_file(output, &re->content[x], sizeof(re->content[x]));
	for ( ; x < re->nr_entries; x++)
		write_file(output, &re->out_of_line_content[x-NR_INLINE_RIPS], sizeof(re->out_of_line_content[0]));
}

static void
maintain_call_stack(IRSB *bb)
{
	unsigned long rip = 0;
	unsigned long endRip;
	int i;
	IRTemp tmp;

	if (bb->jumpkind == Ijk_Call) {
		for (i = bb->stmts_used - 1; !rip && i >= 0; i--)
			if (bb->stmts[i]->tag == Ist_IMark) {
				rip = bb->stmts[i]->Ist.IMark.addr;
				endRip = rip + bb->stmts[i]->Ist.IMark.len;
			}
		if (bb->next->tag == Iex_RdTmp) {
			tmp = bb->next->Iex.RdTmp.tmp;
		} else {
			tmp = newIRTemp(bb->tyenv, Ity_I64);
			addStmtToIRSB(bb,
				      IRStmt_WrTmp(tmp, bb->next));
			bb->next = IRExpr_RdTmp(tmp);
		}
		addStmtToIRSB(bb,
			      IRStmt_Dirty(
				      unsafeIRDirty_0_N(
					      0,
					      "push_call_stack",
					      push_call_stack,
					      mkIRExprVec_1(
						      IRExpr_Const(IRConst_U64(endRip))))));
	}
	if (bb->jumpkind == Ijk_Ret) {
		if (bb->next->tag == Iex_RdTmp) {
			tmp = bb->next->Iex.RdTmp.tmp;
		} else {
			tmp = newIRTemp(bb->tyenv, Ity_I64);
			addStmtToIRSB(bb,
				      IRStmt_WrTmp(tmp, bb->next));
			bb->next = IRExpr_RdTmp(tmp);
		}
		addStmtToIRSB(bb,
			      IRStmt_Dirty(
				      unsafeIRDirty_0_N(
					      0,
					      "pop_call_stack",
					      pop_call_stack,
					      mkIRExprVec_1(
						      IRExpr_RdTmp(tmp)
						      ))));
	}
}

static void
free_rip_entry(struct rip_entry *re)
{
	if (re->nr_entries_allocated > 0) {
		log_free(sizeof(re->out_of_line_content[0]) * re->nr_entries_allocated,
			 mallocer_rip_entry_content);
		VG_(free)(re->out_of_line_content);
	}
}

static void
sanity_check_rip(const struct rip_entry *re)
{
	int x;

	tl_assert(re->nr_entries < 10000000);
	tl_assert(re->rip != 0);
	if (re->nr_entries > NR_INLINE_RIPS)
		tl_assert(re->nr_entries_allocated >= re->nr_entries - NR_INLINE_RIPS);
	for (x = 0; x < re->nr_entries; x++)
		tl_assert(get_re_entry(re, x) != 0);
}
