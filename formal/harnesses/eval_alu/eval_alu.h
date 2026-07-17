#ifndef EVAL_ALU_H
#define EVAL_ALU_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "../eval_sub/eval_sub.h"	/* wrap_diff */
#include "../eval_neg/eval_neg.h"	/* neg_pat */

/*
 * eval_alu is the dispatcher: it masks the operands to the op width
 * (eval_apply_mask / eval_fill_imm), rewrites self-xor to a zeroing
 * MOV, checks operand definedness, and dispatches to the proven
 * operator harnesses. Its contract states the GLUE theorem the
 * verifier's fixpoint loop needs — frame (only rv[dst_reg] changes),
 * error semantics, and the register invariant (ordering, widths, type)
 * re-established on the touched register for the op's width. Per-op
 * VALUE soundness is proven once per operator (usound/ssound in each
 * harness) against the masked operands; eval_apply_mask's own
 * usound/ssound close the loop from the pre-mask register.
 */
/*@
logic uint64_t alu_msk(integer code) =
	BPF_CLASS(code) == BPF_ALU ? (uint64_t)_32_BIT_MASK
				   : (uint64_t)_64_BIT_MASK;

predicate alu_selfxor(struct ebpf_insn ins) =
	BPF_OP(ins.code) == BPF_XOR && BPF_SRC(ins.code) == BPF_X &&
	ins.src_reg == ins.dst_reg;

// The operand-definedness rejection, phrased on the PRE-state TYPES of
// the two referenced registers (dtype/stype — keeping whole-state struct
// loads out of the POs): the dst register is checked unless the op is
// MOV (fully overwritten) or the self-xor idiom (deliberately allowed to
// zero an undefined register); the src register is checked only for
// register sources (immediates are materialised RAW) and never for NEG
// (no source operand).
predicate alu_undef(struct ebpf_insn ins, integer dtype, integer stype) =
	(BPF_OP(ins.code) != EBPF_MOV && !alu_selfxor(ins) &&
	 dtype == RTE_BPF_ARG_UNDEF) ||
	(BPF_OP(ins.code) != BPF_NEG && BPF_SRC(ins.code) == BPF_X &&
	 !alu_selfxor(ins) &&
	 stype == RTE_BPF_ARG_UNDEF);
*/

/*@
// ----------------- Dispatcher-level value soundness -----------------
//
// The theorem reads: whatever concrete values the referenced registers
// could really hold before the instruction, the machine's true result
// for this operation lies within the ranges tracked afterwards. It is
// the glue that turns the per-operator soundness results (usound and
// ssound in each harness, composed with eval_apply_mask's) into one
// guarantee stated on eval_alu itself.

// The machine semantics: the w-bit result PATTERN each dispatched
// operator computes on its operands' patterns (lib/bpf/bpf_exec.c).
// x and y arrive already masked to the op width.
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
	                  y;	// EBPF_MOV

// The ops with a dedicated evaluator. Any other opcode widens the
// destination to full width (eval_max_bound), which contains every
// possible value — there is no per-op semantics left to state.
predicate alu_dispatched(integer op) =
	op == BPF_ADD || op == BPF_SUB || op == BPF_MUL ||
	op == BPF_DIV || op == BPF_MOD || op == BPF_AND ||
	op == BPF_OR  || op == BPF_XOR || op == BPF_LSH ||
	op == BPF_RSH || op == EBPF_ARSH ||
	op == BPF_NEG || op == EBPF_MOV;

// A concrete value the register could hold: pattern within the
// unsigned track AND canonical reading within the signed track (the
// intersection witness — see eval_neg.h), at the register's own mask.
predicate alu_witness(struct bpf_reg_val r, integer x) =
	0 <= x <= r.mask &&
	r.u.min <= x <= r.u.max &&
	r.s.min <= to_signed(x, r.mask) <= r.s.max;

// Operand values the runtime excludes, mirroring the per-operator
// predicates: a zero divisor aborts the program (BPF_DIV_ZERO_CHECK in
// lib/bpf/bpf_exec.c) and oversized shift amounts take the full-width
// path.
predicate alu_op_domain(integer op, integer y, uint64_t msk) =
	((op == BPF_DIV || op == BPF_MOD) ==> 1 <= y) &&
	((op == BPF_LSH || op == BPF_RSH || op == EBPF_ARSH) ==>
		y < op_bits(msk));

// The operand pair (x, y) the instruction could really operate on:
// x is a value dst could hold — except when dst is not read (MOV
// overwrites it; self-xor deliberately zeroes an undefined register —
// the same two exemptions eval_defined grants); y is a value src could
// hold (X source, except NEG which has no source operand), THE SAME
// value as x when both operands name the same register, or the
// materialised immediate (K source).
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

// Both tracks: the new unsigned range contains the result pattern; the
// new signed range contains its canonical (sign-extended) reading.
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

// ---- Composition machinery ------------------------------------------
// The two ATOMIC bridging predicates below name the facts the wit_*
// stones establish; the composition lemmas take them as hypotheses.
// Atomicity is deliberate: an SMT trigger can only match a predicate
// symbol, not a quantified subformula, so folding the stone content
// into named predicates is what lets each straggler leaf close by ONE
// lemma instantiation (the eval_mul folded-lemma recipe).

// Witness transport: every value `before` could hold is, once masked,
// covered by both tracks of `after` (established by apply_mask's
// wsound at each masking call site).
predicate alu_wit_covers(struct bpf_reg_val before,
                         struct bpf_reg_val after, uint64_t msk) =
	\forall integer x;
		alu_witness(before, x) ==>
			after.u.min <= (x & msk) <= after.u.max &&
			after.s.min <= to_signed(x & msk, msk) <= after.s.max;

// K-source operand: ms pins the materialised immediate exactly
// (established by eval_fill_imm's const_u/const_s).
predicate alu_imm_covers(struct bpf_reg_val ms, struct ebpf_insn ins,
                         uint64_t msk) =
	ms.u.min == (((uint64_t)ins.imm) & msk) && ms.u.max == ms.u.min &&
	ms.s.min == to_signed(((uint64_t)ins.imm) & msk, msk) &&
	ms.s.max == ms.s.min;

// Shared hypothesis bundle of every composition lemma: the op shape,
// dst transport, and the mode-cased src coverage.
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

#endif /* EVAL_ALU_H */
