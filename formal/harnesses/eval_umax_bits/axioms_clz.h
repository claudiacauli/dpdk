#ifndef AXIOMS_CLZ_H
#define AXIOMS_CLZ_H

#include "../../common/shared.h"

/*
 * Trusted axioms used ONLY by the eval_umax_bits proof (and its
 * dependents). Must be kept out of common/axioms.h because quantified
 * axioms perturb the SMT search of every PO in whose translation unit
 * they appear, even when their triggers cannot fire. Include
 * from eval_umax_bits.h only.
 *
 * They bridge rte_clz64's contract fact `(v >> (63 - r)) == 1` (the
 * leading-one window) to linear facts about `allones >> r`, which is
 * exactly the term RTE_LEN2MASK(64 - r, uint64_t) reduces to in the
 * POs of the FIX_UMAX_BITS_32 body.
 */
/*@
axiomatic ClzWindow {

	// v lives under its own bit-length mask. Window pins v < 2^(64-r).
	axiom clz_window_hi:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> v <= (_64_BIT_MASK >> r);

	// v lives above half of its own bit-length mask. The leading one
	// contributes 2^(63-r). Needed by `tight` and by the `width` chain.
	axiom clz_window_lo:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> ((_64_BIT_MASK >> r) >> 1) < v;

	// allones >> r is an all-ones value 2^(64-r) - 1. Needed by `shape`
	// as it establishes its ensures in land form.
	axiom allones_shr_shape:
		\forall integer r;
		0 <= r <= 63
		==> ((_64_BIT_MASK >> r) & ((_64_BIT_MASK >> r) + 1)) == 0;

	// 32-bit width: an in-width v (<= 2^32-1) has its leading one at
	// bit <= 31, so its bit-length mask also fits 32 bits. The 64-bit
	// case is lsr_shrink (allones >> r <= allones), already shared.
	axiom clz_mask_width_32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= _32_BIT_MASK
		==> (_64_BIT_MASK >> r) <= _32_BIT_MASK;

	// Half-width refinements of the same shape: a v under msk>>1 has
	// its leading one at bit <= w-2, so its bit-length mask also fits
	// under msk>>1. Carries the sord/swidth goals of the callers (the
	// signed track stores eval_uand_max results, and to_sint64 only
	// collapses once the result is pinned under 2^63).
	axiom clz_mask_half32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFF
		==> (_64_BIT_MASK >> r) <= 0x7FFFFFFF;

	axiom clz_mask_half64:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFFFFFFFFFF
		==> (_64_BIT_MASK >> r) <= 0x7FFFFFFFFFFFFFFF;
}
*/

#endif /* AXIOMS_CLZ_H */
