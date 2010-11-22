/* This is shared between FT and FT2.  I've no idea how to do a
   library common to two components in Automake, so just do it by
   #include'ing the relevant .c file. */

static void do_store(unsigned long addr, unsigned long data, unsigned long size,
		     unsigned long rsp, unsigned long rip);
static void do_store2(unsigned long addr, unsigned long x1, unsigned long x2,
		      unsigned long rsp, unsigned long rip);

static IRTemp
cast_to_U64(IRSB *irsb, IRExpr *expr)
{
	IROp op;
	IRTemp tmp;

	switch (typeOfIRExpr(irsb->tyenv, expr)) {
	case Ity_I8:
		op = Iop_8Uto64;
		break;
	case Ity_I16:
		op = Iop_16Uto64;
		break;
	case Ity_I32:
		op = Iop_32Uto64;
		break;
	case Ity_F64:
		op = Iop_ReinterpF64asI64;
		break;
	case Ity_F32:
		tmp = newIRTemp(irsb->tyenv, Ity_I32);
		addStmtToIRSB(irsb,
			      IRStmt_WrTmp(tmp,
					   IRExpr_Unop(Iop_ReinterpF32asI32,
						       expr)));
		return cast_to_U64(irsb,
				   IRExpr_RdTmp(tmp));
	default:
		VG_(tool_panic)((Char *)"Weird-arse type problem.\n");
	}
	tmp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(tmp,
				   IRExpr_Unop(op, expr)));
	return tmp;
}

static void
add_dirty_call(IRSB *irsb,
	       char *name,
	       void *ptr,
	       ...)
{
	va_list args;
	int nr_args;
	IRExpr *e;
	IRExpr **arg_v;
	IRDirty *dirty;

	va_start(args, ptr);
	nr_args = 0;
	while (1) {
		e = va_arg(args, IRExpr *);
		if (!e)
			break;
		nr_args++;
	}
	va_end(args);

	arg_v = LibVEX_Alloc( (nr_args + 1) * sizeof(arg_v[0]) );
	va_start(args, ptr);
	nr_args = 0;
	while (1) {
		e = va_arg(args, IRExpr *);
		if (!e)
			break;
		arg_v[nr_args] = e;
		nr_args++;
	}
	arg_v[nr_args] = NULL;
	va_end(args);

	dirty = unsafeIRDirty_0_N(0, name, ptr, arg_v);
	addStmtToIRSB(irsb, IRStmt_Dirty(dirty) );
}


static void
constructLoggingStore(IRSB *irsb,
		      IRExpr *addr,
		      IRExpr *data,
		      unsigned long rip)
{
	IRType t = typeOfIRExpr(irsb->tyenv, data);
	IRTemp tmp1, tmp2;
	int is_vector = 0;
	IRTemp rsp;

	rsp = newIRTemp(irsb->tyenv, Ity_I64);
	addStmtToIRSB(irsb,
		      IRStmt_WrTmp(rsp,
				   IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
	switch (t) {
	case Ity_I8:
	case Ity_I16:
	case Ity_I32:
	case Ity_F32:
	case Ity_F64:
		tmp1 = cast_to_U64(irsb, data);
		add_dirty_call(irsb,
			       "do_store",
			       do_store,
			       addr,
			       IRExpr_RdTmp(tmp1),
			       IRExpr_Const(IRConst_U64(sizeofIRType(t))),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	case Ity_I64:
		add_dirty_call(irsb,
			       "do_store",
			       do_store,
			       addr,
			       data,
			       IRExpr_Const(IRConst_U64(8)),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	case Ity_V128:
		is_vector = 1;
	case Ity_I128:
		tmp1 = newIRTemp(irsb->tyenv, Ity_I64);
		tmp2 = newIRTemp(irsb->tyenv, Ity_I64);
		addStmtToIRSB(
			irsb,
			IRStmt_WrTmp(
				tmp1,
				IRExpr_Unop(
					is_vector ? Iop_V128to64 : Iop_128to64,
					data)));
		addStmtToIRSB(
			irsb,
			IRStmt_WrTmp(
				tmp2,
				IRExpr_Unop(
					is_vector ? Iop_V128HIto64 : Iop_128HIto64,
					data)));
		add_dirty_call(irsb,
			       "do_store2",
			       do_store2,
			       addr,
			       IRExpr_RdTmp(tmp1),
			       IRExpr_RdTmp(tmp2),
			       IRExpr_RdTmp(rsp),
			       IRExpr_Const(IRConst_U64(rip)),
			       NULL);
		break;
	default:
		VG_(tool_panic)("Store of unexpected type\n");
	}
}

static void
log_call(unsigned long ret_addr, unsigned long callee)
{
	ThreadId tid = VG_(get_running_tid)();
	struct thread_extra_data *ted;
	unsigned h = tid % NR_THREAD_EXTRA_HEADS;

	for (ted = thread_extra_heads[h];
	     ted && ted->tid != tid;
	     ted = ted->next)
		;
	if (!ted) {
		ted = VG_(malloc)("thread_extra_data", sizeof(*ted));
		ted->tid = tid;
		ted->next = thread_extra_heads[h];
		ted->nr_stack_slots = 0;
		ted->nr_stack_slots_allocated = 16;
		ted->stack = VG_(malloc)("Thread stack", sizeof(ted->stack[0]) * ted->nr_stack_slots_allocated);
		thread_extra_heads[h] = ted;
	}
	if (ted->nr_stack_slots == ted->nr_stack_slots_allocated) {
		ted->nr_stack_slots_allocated *= 2;
		ted->stack = VG_(realloc)("Thread stack",
					  ted->stack,
					  sizeof(ted->stack[0]) * ted->nr_stack_slots_allocated);
	}
	ted->stack[ted->nr_stack_slots] = ret_addr;
	ted->nr_stack_slots++;
}

static void
log_return(unsigned long to, unsigned long rip)
{
	ThreadId tid = VG_(get_running_tid)();
	struct thread_extra_data *ted;
	unsigned h = tid % NR_THREAD_EXTRA_HEADS;
	int x;

	for (ted = thread_extra_heads[h];
	     ted && ted->tid != tid;
	     ted = ted->next)
		;

	tl_assert(ted);
	for (x = ted->nr_stack_slots - 1; x >= 0; x--) {
		if (ted->stack[x] == to) {
			if (x != ted->nr_stack_slots - 1)
				VG_(printf)("Returning to something other than the calling function; did someone call longjmp?\n");
			ted->nr_stack_slots = x;
			return;
		}
	}
	VG_(printf)("Returning to somewhere we never came from... (%lx)\n", to);
	ted->nr_stack_slots = 0;
}

static IRSB *
log_stores(IRSB *bb)
{
	IRSB *out = deepCopyIRSBExceptStmts(bb);
	int x;
	IRStmt *stmt;
	unsigned long instr_start;

	instr_start = 0xcafebabedeadbeef;
	for (x = 0; x < bb->stmts_used; x++) {
		stmt = bb->stmts[x];
		if (stmt->tag != Ist_Store) {
			addStmtToIRSB(out, stmt);
		} else {
			constructLoggingStore(out,
					      stmt->Ist.Store.addr,
					      stmt->Ist.Store.data,
					      instr_start);
		}
		if (stmt->tag == Ist_IMark)
			instr_start = stmt->Ist.IMark.addr;
	}
	return out;
}

static IRSB *
log_call_return(IRSB *bb)
{
	unsigned long instr_end;
	unsigned long instr_start;
	int x;
	IRStmt *stmt;

	instr_start = 0xdeadbeefbabe;
	instr_end = 0xf001beefdeadcafe;
	for (x = bb->stmts_used - 1; x >= 0; x--) {
		stmt = bb->stmts[x];
		if (stmt->tag == Ist_IMark) {
			instr_start = stmt->Ist.IMark.addr;
			instr_end = stmt->Ist.IMark.addr + stmt->Ist.IMark.len;
			break;
		}
	}
	tl_assert(x >= 0);

	if (bb->jumpkind == Ijk_Call)
		add_dirty_call(bb,
			       "log_call",
			       log_call,
			       IRExpr_Const(IRConst_U64(instr_end)),
			       bb->next,
			       NULL);
	else if (bb->jumpkind == Ijk_Ret)
		add_dirty_call(bb,
			       "log_return",
			       log_return,
			       bb->next,
			       IRExpr_Const(IRConst_U64(instr_end)),
			       NULL);

	return bb;
}

