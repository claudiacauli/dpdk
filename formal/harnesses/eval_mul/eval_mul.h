#ifndef EVAL_MUL_H
#define EVAL_MUL_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_mul_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, w;
		bin_witness(od, os, v, w, msk)
			==> nw.s.min <= to_signed((v * w) & msk, msk) <= nw.s.max;

predicate eval_mul_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= ((x * y) & msk) <= nw.u.max;

// Overflow-branch soundness as a LEMMA whose conclusion is the folded
// predicate: proved once (= the isolated mask-strip + framing, seconds),
// then each overflow soundness goal closes by ONE instantiation. Its trigger
// is the predicate application (rare — only the soundness goals), so it
// cannot perturb; it replaces the per-goal e-matching search that explodes
// in the full heap context (the overflow x smax-fallback combination times
// out even at 1800s otherwise). Bracket hypotheses (nw brackets the corner
// products; product fits the width) so it applies through the C multiply's
// to_uint64 with no separate no-wrap step.
lemma mul_usound_overflow:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(msk & (msk + 1)) == 0 &&
		0 <= od.u.min <= od.u.max && 0 <= os.u.min <= os.u.max &&
		nw.u.min <= od.u.min * os.u.min &&
		od.u.max * os.u.max <= nw.u.max &&
		od.u.max * os.u.max <= msk
		==> eval_mul_unsigned_soundness(od, os, nw, msk);

// Signed both-non-negative overflow branch, the ssound twin: v,w >= 0 and the
// product fits below msk>>1, so to_signed strips to the product and the corner
// products bracket every witness. Same instantiation strategy.
lemma mul_ssound_overflow:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(msk & (msk + 1)) == 0 &&
		0 <= od.s.min <= od.s.max && 0 <= os.s.min <= os.s.max &&
		nw.s.min <= od.s.min * os.s.min &&
		od.s.max * os.s.max <= nw.s.max &&
		od.s.max * os.s.max <= (msk >> 1)
		==> eval_mul_signed_soundness(od, os, nw, msk);

// Constants-branch soundness, the third folded lemma (diagnosed
// 2026-07-20: the U1 usound split family, parts 01..10, is the
// both-u-constant path, where mul_usound_overflow cannot fire — its
// `product <= msk` hypothesis is false there; that is exactly why the
// code masks). Both u ranges pinned to a point, so every witness pair
// IS (od.u.min, os.u.min) and the masked product equals the stored
// endpoints by congruence — no mask-strip needed, the mask stays on
// both sides. Closes the family by one instantiation, like the
// overflow twins.
//
// (A PROVE_MUL_SOUND gate briefly wrapped these two lemmas while a
// swidth regression was bisected, 2026-07-20. Post-mortem: swidth is a
// CLIFF goal at margin zero — removing any one addition, these lemmas
// included, did NOT restore it; the real fix was the opsz case split,
// SPLIT_PROPS+=swidth in the driver. The lemmas are ungated again.)
lemma mul_usound_const:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		od.u.min == od.u.max && os.u.min == os.u.max &&
		nw.u.min <= ((od.u.min * os.u.min) & msk) &&
		((od.u.max * os.u.max) & msk) <= nw.u.max
		==> eval_mul_unsigned_soundness(od, os, nw, msk);

// Signed constants branch, the ssound twin (the S1 family, split parts
// 1 + 11k: both-s-constant path via mul_sext2). Both s ranges pinned,
// so to_signed pins each witness pattern to its constant's pattern;
// mul_sext_congr (axioms_mul.h) then equates the witness pattern
// product with the canonical product under the mask, and the brackets
// close. The u-track hypotheses only bound the witnesses within the
// width for the congruence guard.
lemma mul_ssound_const:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		0 <= od.u.min && od.u.max <= msk &&
		0 <= os.u.min && os.u.max <= msk &&
		od.s.min == od.s.max && os.s.min == os.s.max &&
		nw.s.min <= to_signed((od.s.min * os.s.min) & msk, msk) &&
		to_signed((od.s.max * os.s.max) & msk, msk) <= nw.s.max
		==> eval_mul_signed_soundness(od, os, nw, msk);

// OP-OPTIMALITY (mul-optimal). Each output endpoint is ATTAINED by a
// representable input PAIR (bin_witness). PRELIMINARY (optimality_notes.md);
// nonlinear but corner-based on non-negatives (products are monotone there), so
// Category A: op-optimal from SELF-OPTIMAL operands in the no-overflow regime;
// the signed track only when BOTH operands are non-negative (mixed signs widen).
predicate eval_mul_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x * y) & msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x * y) & msk) == nw.u.min);

predicate eval_mul_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                  struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer v, w; bin_witness(od, os, v, w, msk) && to_signed((v * w) & msk, msk) == nw.s.max) &&
	(\exists integer v, w; bin_witness(od, os, v, w, msk) && to_signed((v * w) & msk, msk) == nw.s.min);
*/

void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_MUL_H */
