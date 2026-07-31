#ifndef EVAL_ALU_H
#define EVAL_ALU_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_neg/eval_neg.h"

/*@
logic uint64_t alu_msk(integer code) =
	BPF_CLASS(code) == BPF_ALU ? (uint64_t)_32_BIT_MASK
				   : (uint64_t)_64_BIT_MASK;

predicate alu_selfxor(struct ebpf_insn ins) =
	BPF_OP(ins.code) == BPF_XOR && BPF_SRC(ins.code) == BPF_X &&
	ins.src_reg == ins.dst_reg;

predicate alu_undef(struct ebpf_insn ins, integer dtype, integer stype) =
	(BPF_OP(ins.code) != EBPF_MOV && !alu_selfxor(ins) &&
	 dtype == RTE_BPF_ARG_UNDEF) ||
	(BPF_OP(ins.code) != BPF_NEG && BPF_SRC(ins.code) == BPF_X &&
	 !alu_selfxor(ins) &&
	 stype == RTE_BPF_ARG_UNDEF);
*/

/*@

logic integer alu_op_pat(integer op, integer x, integer y, uint64_t msk) =
	op == BPF_ADD   ? ((x + y) & msk) :
	op == BPF_SUB   ? wrap_diff(x - y, msk) :
	op == BPF_MUL   ? ((x * y) & msk) :
	op == BPF_DIV   ? x / y :
	op == BPF_MOD   ? x % y :
	op == BPF_AND   ? (x & y) :
	op == BPF_OR    ? (x | y) :
	op == BPF_XOR   ? (x ^ y) :
	op == BPF_LSH   ? ((x << y) & msk) :
	op == BPF_RSH   ? (x >> y) :
	op == EBPF_ARSH ? (((uint64_t)(to_signed(x, msk) >> y)) & msk) :
	op == BPF_NEG   ? neg_pat(x, msk) :
	                  y;

predicate alu_dispatched(integer op) =
	op == BPF_ADD || op == BPF_SUB || op == BPF_MUL ||
	op == BPF_DIV || op == BPF_MOD || op == BPF_AND ||
	op == BPF_OR  || op == BPF_XOR || op == BPF_LSH ||
	op == BPF_RSH || op == EBPF_ARSH ||
	op == BPF_NEG || op == EBPF_MOV;

predicate alu_witness(struct bpf_reg_val r, integer x) =
	0 <= x <= r.mask &&
	r.u.min <= x <= r.u.max &&
	r.s.min <= to_signed(x, r.mask) <= r.s.max;

predicate alu_op_domain(integer op, integer y, uint64_t msk) =
	((op == BPF_DIV || op == BPF_MOD) ==> 1 <= y) &&
	((op == BPF_LSH || op == BPF_RSH || op == EBPF_ARSH) ==>
		y < op_bits(msk));

predicate alu_operands(struct bpf_reg_val dst_before,
                       struct bpf_reg_val src_before,
                       struct ebpf_insn ins, integer x, integer y) =
	\let op  = BPF_OP(ins.code);
	\let msk = alu_msk(ins.code);
	(op != EBPF_MOV && !alu_selfxor(ins) ==>
		alu_witness(dst_before, x)) &&
	(BPF_SRC(ins.code) == BPF_X
		? ((op != BPF_NEG ==> alu_witness(src_before, y)) &&
		   (ins.src_reg == ins.dst_reg ==> y == x))
		: y == (((uint64_t)ins.imm) & msk)) &&
	alu_op_domain(op, y & msk, msk);

predicate eval_alu_unsigned_soundness(struct bpf_reg_val dst_before,
                                      struct bpf_reg_val src_before,
                                      struct ebpf_insn ins,
                                      struct bpf_reg_val dst_after) =
	\let op  = BPF_OP(ins.code);
	\let msk = alu_msk(ins.code);
	alu_dispatched(op) ==>
	\forall integer x, y;
		alu_operands(dst_before, src_before, ins, x, y)
			==> dst_after.u.min
			    <= alu_op_pat(op, x & msk, y & msk, msk)
			    <= dst_after.u.max;

predicate eval_alu_signed_soundness(struct bpf_reg_val dst_before,
                                    struct bpf_reg_val src_before,
                                    struct ebpf_insn ins,
                                    struct bpf_reg_val dst_after) =
	\let op  = BPF_OP(ins.code);
	\let msk = alu_msk(ins.code);
	alu_dispatched(op) ==>
	\forall integer x, y;
		alu_operands(dst_before, src_before, ins, x, y)
			==> dst_after.s.min
			    <= to_signed(alu_op_pat(op, x & msk, y & msk, msk),
			                 msk)
			    <= dst_after.s.max;

predicate alu_wit_covers(struct bpf_reg_val before,
                         struct bpf_reg_val after, uint64_t msk) =
	\forall integer x;
		alu_witness(before, x) ==>
			after.u.min <= (x & msk) <= after.u.max &&
			after.s.min <= to_signed(x & msk, msk) <= after.s.max;

predicate alu_imm_covers(struct bpf_reg_val ms, struct ebpf_insn ins,
                         uint64_t msk) =
	ms.u.min == (((uint64_t)ins.imm) & msk) && ms.u.max == ms.u.min &&
	ms.s.min == to_signed(((uint64_t)ins.imm) & msk, msk) &&
	ms.s.max == ms.s.min;

predicate alu_compose_pre(struct bpf_reg_val od, struct bpf_reg_val os,
                          struct bpf_reg_val md, struct bpf_reg_val ms,
                          struct ebpf_insn ins, uint64_t msk) =
	msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
	alu_wit_covers(od, md, msk) &&
	(BPF_SRC(ins.code) == BPF_X
		? alu_wit_covers(os, ms, msk)
		: alu_imm_covers(ms, ins, msk));
*/

const char *eval_alu(struct bpf_verifier *bvf, const struct ebpf_insn *ins);

#endif
