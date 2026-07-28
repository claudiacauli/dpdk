/*
 * EXPERIMENT TU — NOT in any verify_all.sh pass. Phase A of the
 * composition-theorem effort (un-parking eval_alu's usound/ssound):
 * try the two SIGNED composition lemmas predicted to prove WITHOUT a
 * low-bit congruence bridge (axioms_alu_signed.h's "TRY FIRST" pair —
 * divmod states both tracks over u already; neg carries the
 * intersection witness). Stated here in isolation so that (a) the ten
 * unproved signed twins stay out of scope (fake-proof hazard), and
 * (b) a red here cannot perturb any green pass.
 *
 * Run (lemma goals need a NON -wp-fct pass):
 *   frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-par <N> \
 *       -wp-timeout 300 -wp-prop @lemma \
 *       harnesses/eval_alu/compose_try_signed.c
 */
#include "eval_alu.h"
#include "../eval_divmod/eval_divmod.h"

/*@
lemma alu_compose_divmod_s_try:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		(BPF_OP(ins.code) == BPF_DIV ||
		 BPF_OP(ins.code) == BPF_MOD) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_divmod_signed_soundness(BPF_OP(ins.code), md, ms,
			nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_neg_s_try:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_NEG &&
		msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
		alu_wit_covers(od, md, msk) &&
		eval_neg_signed_soundness(md, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);
*/
