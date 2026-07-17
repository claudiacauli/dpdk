#ifndef AXIOMS_ALU_SIGNED_H
#define AXIOMS_ALU_SIGNED_H

/*
 * PARKED — NOT INCLUDED BY ANY TU, DELIBERATELY.
 *
 * These are the signed twins of the alu_compose_* lemmas in
 * axioms_alu.h. They are STATED but NOT PROVED: including them would
 * put unproven lemmas in scope of every eval_alu PO, and WP ASSUMES
 * every lemma in scope — so any goal could close on an unproven
 * hypothesis (the fake-proof hazard). Nothing here may be included
 * until each lemma below is proved by the driver's @lemma pass.
 *
 * WHY THEY DO NOT PROVE AS-IS (measured 2026-07-16: the unsigned
 * twins prove in 2-3s each; alu_compose_and_s times out at 605s):
 * a WITNESS-SHAPE mismatch, not a search failure. Each operator's
 * *_signed_soundness quantifies its DST witness over the CANONICAL
 * track (od.s.min <= v <= od.s.max), while the dispatcher-level
 * predicate quantifies w-bit PATTERNS. Chaining them needs the
 * low-w-bit CONGRUENCE facts below — sign-extending an operand cannot
 * change the low w bits of the result. All are full-domain bitwise /
 * modular-arithmetic facts, i.e. the ESBMC-validation class (see
 * formal/README.md; cf. common/axioms_and.h's to_signed_land_pat,
 * which is eval_and's own internal version of this idea).
 *
 * Per-operator status:
 *   divmod  - composes DIRECTLY (both tracks already over u) - PROVED
 *             in axioms_alu.h? no: only the _u twin; the _s twin needs
 *             no bridge and should prove as-is - TRY FIRST.
 *   neg     - composes DIRECTLY (intersection witness) - TRY FIRST.
 *   and     - needs land_sext_lo: (to_signed(p,m) & q) == (p & q)
 *   or/xor  - twins of the above, with the trailing & m
 *   lsh/rsh - need the pattern round-trip
 *             ((uint64_t)to_signed(p,m)) & m == p; MAY be derivable
 *             from to_signed_pattern_id (common/axioms_and.h:102)
 *   arsh    - via to_signed_pattern_id
 *   add     - ((uint64_t)v + (uint64_t)w) & m == (p + q) & m
 *   sub     - wrap_diff congruence; CARE: wrap_diff models ONE wrap
 *             only, so check the |v - w| vs |p - q| ranges first
 *   mul     - eval_mul's existing mul_mask_wrap may already serve
 *
 * Order of work: divmod_s + neg_s (no bridge) -> validate the bridge
 * axioms with ESBMC -> the remaining nine. Then include this header
 * from eval_alu.c, add the lemmas to the axioms_alu.h @lemma pass, and
 * restore the ssound ensures in eval_alu.c.
 */

/*@
lemma alu_compose_add_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_ADD &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_add_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_sub_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_SUB &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_sub_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_mul_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_MUL &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_mul_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_divmod_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		(BPF_OP(ins.code) == BPF_DIV ||
		 BPF_OP(ins.code) == BPF_MOD) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_divmod_signed_soundness(BPF_OP(ins.code), md, ms,
			nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_and_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_AND &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_and_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_or_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_OR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_or_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_xor_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_XOR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_xor_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_lsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_lsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_rsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_rsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_arsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_ARSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_arsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_neg_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_NEG &&
		msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
		alu_wit_covers(od, md, msk) &&
		eval_neg_signed_soundness(md, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

// Self-xor rewrites to a zeroing: y is forced equal to x, so the
// result pattern is identically 0 and the zeroed register pins it.
lemma alu_compose_selfxor_s:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.s.min == 0 && nw.s.max == 0
		==> eval_alu_signed_soundness(od, os, ins, nw);
*/

#endif /* AXIOMS_ALU_SIGNED_H */
