#ifndef AXIOMS_ALU_H
#define AXIOMS_ALU_H

#include "eval_alu.h"
#include "../eval_apply_mask/eval_apply_mask.h"
#include "../eval_add/eval_add.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_lsh/eval_lsh.h"
#include "../eval_rsh/eval_rsh.h"
#include "../eval_arsh/eval_arsh.h"
#include "../eval_and/eval_and.h"
#include "../eval_or/eval_or.h"
#include "../eval_xor/eval_xor.h"
#include "../eval_mul/eval_mul.h"
#include "../eval_divmod/eval_divmod.h"
#include "../eval_neg/eval_neg.h"

/*
 * PARKED — NOT INCLUDED BY ANY TU (deliberately; see eval_alu.c).
 *
 * Composition lemmas for eval_alu's dispatcher-level usound (the SIGNED
 * twins are in axioms_alu_signed.h). Every one of these 12 unsigned
 * lemmas is MACHINE-PROVED — each closes in 2-3s isolated (WITHOUT
 * -wp-fct: under -wp-fct WP schedules no lemma goals) — and the lemma
 * APPLICATION works too (given its hypotheses, the dispatcher goal for
 * an arm closes in ~3s). They are parked only because the missing piece
 * is delivering each lemma its hypotheses per dispatch arm: that needs a
 * masked-operand struct value bridged across the eval_defined call, and
 * that heap plumbing (es_add/pre_add relay stones) times out at ~247s.
 * To finish: make the per-arm coverage + operator-soundness facts prove
 * cheaply (a ghost value alone did not suffice), then re-include this
 * header, add it back to a NON -wp-fct @lemma pass in verify_all.sh, and
 * restore the usound ensures in eval_alu.c.
 *
 * One lemma per operator: destination/source witness coverage plus the
 * operator's own soundness at the masked operands imply the
 * dispatcher-level soundness. Each is pure first-order logic over
 * struct values — no heap. The trigger is the atomic alu_wit_covers /
 * alu_imm_covers a per-arm stone would establish (an SMT trigger
 * matches a predicate symbol, never a quantified subformula — hence the
 * folding).
 *
 * The SIGNED twins are parked in axioms_alu_signed.h, unproved and
 * deliberately not included; see that file for the diagnosis.
 */
/*@
lemma alu_compose_add_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_ADD &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_add_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_sub_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_SUB &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_sub_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_mul_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_MUL &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_mul_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_divmod_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		(BPF_OP(ins.code) == BPF_DIV ||
		 BPF_OP(ins.code) == BPF_MOD) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_divmod_unsigned_soundness(BPF_OP(ins.code), md, ms,
			nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_and_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_AND &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_and_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_or_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_OR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_or_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_xor_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_XOR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_xor_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_lsh_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_lsh_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_rsh_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_rsh_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_arsh_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_ARSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_arsh_unsigned_soundness(md, ms, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_neg_u:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_NEG &&
		msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
		alu_wit_covers(od, md, msk) &&
		eval_neg_unsigned_soundness(md, nw, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

// Self-xor rewrites to a zeroing: y is forced equal to x, so the
// result pattern is identically 0 and the zeroed register pins it.
lemma alu_compose_selfxor_u:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.u.min == 0 && nw.u.max == 0
		==> eval_alu_unsigned_soundness(od, os, ins, nw);
*/

#endif /* AXIOMS_ALU_H */
