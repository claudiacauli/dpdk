#ifndef AXIOMS_CLZ_H
#define AXIOMS_CLZ_H

#include "shared.h"

/*
 * Trusted axioms used ONLY by the eval_umax_bits proof (and its
 * dependents), deliberately kept out of common/axioms.h: quantified
 * axioms perturb the SMT search of every PO in whose translation unit
 * they appear, even when their triggers cannot fire (see
 * common/axioms_arsh.h for the incident that taught us this). Include
 * from eval_umax_bits.h only. Same trust contract as axioms.h: every
 * axiom is CBMC-proved in axiom_validation/validate_specs_axioms.c.
 *
 * They bridge rte_clz64's contract fact `(v >> (63 - r)) == 1` (the
 * leading-one window) to linear facts about `allones >> r`, which is
 * exactly the term RTE_LEN2MASK(64 - r, uint64_t) reduces to in the
 * POs of the FIX_UMAX_BITS_32 body.
 */
/*@
axiomatic ClzWindow {
	// v lives under its own bit-length mask: window pins v < 2^(64-r).
	axiom clz_window_hi:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> v <= (0xFFFFFFFFFFFFFFFF >> r);
	// ...and above half of it: the leading one contributes 2^(63-r).
	// Carries `tight`, and (via lsr_amt_anti) the width chain.
	axiom clz_window_lo:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> ((0xFFFFFFFFFFFFFFFF >> r) >> 1) < v;
	// allones >> r is an all-ones value 2^(64-r) - 1: the `shape`
	// ensures in land form.
	axiom allones_shr_shape:
		\forall integer r;
		0 <= r <= 63
		==> ((0xFFFFFFFFFFFFFFFF >> r) & ((0xFFFFFFFFFFFFFFFF >> r) + 1)) == 0;
	// 32-bit width: an in-width v (<= 2^32-1) has its leading one at
	// bit <= 31, so its bit-length mask also fits 32 bits. The 64-bit
	// case is lsr_shrink (allones >> r <= allones), already shared.
	axiom clz_mask_width_32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0xFFFFFFFF
		==> (0xFFFFFFFFFFFFFFFF >> r) <= 0xFFFFFFFF;
	// Half-width refinements of the same shape: a v under msk>>1 has
	// its leading one at bit <= w-2, so its bit-length mask also fits
	// under msk>>1. Carries the sord/swidth goals of the callers (the
	// signed track stores eval_uand_max results, and to_sint64 only
	// collapses once the result is pinned under 2^63).
	axiom clz_mask_half32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFF
		==> (0xFFFFFFFFFFFFFFFF >> r) <= 0x7FFFFFFF;
	axiom clz_mask_half64:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFFFFFFFFFF
		==> (0xFFFFFFFFFFFFFFFF >> r) <= 0x7FFFFFFFFFFFFFFF;
}
*/

#endif /* AXIOMS_CLZ_H */
