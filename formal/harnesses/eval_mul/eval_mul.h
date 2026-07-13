#ifndef EVAL_MUL_H
#define EVAL_MUL_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_mul_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, w;
		od.s.min <= v <= od.s.max && os.s.min <= w <= os.s.max
			==> nw.s.min <= to_signed((v * w) & msk, msk) <= nw.s.max;

predicate eval_mul_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max
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
*/

void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_MUL_H */
