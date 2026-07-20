#ifndef AXIOMS_MUL_H
#define AXIOMS_MUL_H

#include "../../common/specs.h"

/*
 * Trusted axioms used ONLY by the eval_mul proof, TU-scoped like the
 * other axioms_*.h headers (include from eval_mul.c only). Same trust
 * contract: every axiom is CBMC-proved over its full domain in
 * axiom_validation/validate_specs_axioms.c.
 *
 * Multiplication is NONLINEAR, which WP's SMT back-ends (Alt-Ergo especially)
 * cannot reason about — even `u.min <= u.max ==> u.min*k <= u.max*k` is out
 * of reach. These give the linear facts the range analysis needs: products
 * of non-negatives are non-negative and monotone, and a product of two
 * half-width-bounded operands fits in the full width (the soundness of the
 * FIX_MUL_UGUARD / FIX_MUL_SGUARD overflow guards). The bound axioms are
 * mask-concrete so they fire after the opsz case split without an
 * instantiation search, like the land_/lor_ mask families.
 */
/*@
axiomatic MulBounds {
	axiom mul_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a * b);
	// Monotonicity — THE workhorse: carries range ordering (min*min <=
	// max*max) and the soundness upper bound (x*y <= max_d*max_s for any
	// witness pair beneath the tracked maxima).
	axiom mul_mono:
		\forall integer a, b, c, d;
		0 <= a <= c && 0 <= b <= d ==> (a * b) <= (c * d);
	// Overflow guards: both operands under 2^(w/2) keep the UNSIGNED
	// product within 2^w-1 (FIX_MUL_UGUARD: msk >> opsz/2). Mask-concrete
	// for the two widths.
	axiom mul_bound_u32:
		\forall integer a, b;
		0 <= a <= 0xFFFF && 0 <= b <= 0xFFFF ==> (a * b) <= 0xFFFFFFFF;
	axiom mul_bound_u64:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
		==> (a * b) <= 0xFFFFFFFFFFFFFFFF;
	// Both operands under 2^((w-1)/2) keep the SIGNED product within
	// 2^(w-1)-1 = msk>>1 (FIX_MUL_SGUARD: (msk>>1) >> opsz/2).
	axiom mul_bound_s32:
		\forall integer a, b;
		0 <= a <= 0x7FFF && 0 <= b <= 0x7FFF ==> (a * b) <= 0x7FFFFFFF;
	axiom mul_bound_s64:
		\forall integer a, b;
		0 <= a <= 0x7FFFFFFF && 0 <= b <= 0x7FFFFFFF
		==> (a * b) <= 0x7FFFFFFFFFFFFFFF;
	// Low-w bits of a product are wrap-invariant. BOTH constants branches
	// compute the product in uint64 (with its 2^64 wrap) before masking by
	// msk, while the soundness predicates mask the MATHEMATICAL product;
	// for the two full masks (w <= 64) the low w bits agree, so the masked
	// values are equal — WP's Cbits + nonlinear encoding cannot relate
	// them. Discharged ONLY inside the mul_umask / mul_sext2 helper VCs
	// (mul_sext2 by congruence, applying to_signed to both equal sides);
	// the helpers' math-form `ensures` keep this uint-product form
	// `to_uint64(to_uint64(a)*to_uint64(b))` out of every eval_mul
	// soundness goal, so the axiom never fires there — inline it perturbs
	// (the bidirectional equality matching-loops on the constants term and
	// times out even the trivial all-constant part).
	axiom mul_mask_wrap:
		\forall integer a, b, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF)
		==> (((uint64_t)((uint64_t)a * (uint64_t)b)) & m) == ((a * b) & m);
	// Low-w bits of a product depend only on the operands' low-w bits:
	// a w-bit pattern and its sign-extended canonical value are
	// congruent mod 2^w, so their products agree under the mask.
	// Gated to the @lemma pass (PROVE_MUL_LEMMAS): this axiom exists
	// only to PROVE mul_ssound_const, and the trigger design (fire only
	// on the co-occurrence of both conclusion terms) did NOT survive
	// contact with the solvers — with the axiom in the main TU, swidth
	// regressed 1m-green -> 300s-spin and the optimality cell flipped
	// which goals close (2026-07-20). The soundness passes only need
	// the LEMMA assumed, so the axiom stays out of their TU entirely;
	// the driver's axioms_mul lemma pass compiles with
	// -DPROVE_MUL_LEMMAS and proves the lemma with the axiom in scope.
	// ESBMC validation cell in validate_specs_axioms.c (server: the
	// 64-bit multiplier is intractable for this Mac's ESBMC; local
	// evidence = exhaustive w=4/8/12 brute force, zero violations).
#ifdef PROVE_MUL_LEMMAS
	axiom mul_sext_congr:
		\forall integer v, w, c, e, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= v <= m && 0 <= w <= m &&
		to_signed(v, m) == c && to_signed(w, m) == e
		==> to_signed((v * w) & m, m) == to_signed((c * e) & m, m);
#endif
}
*/

// Ground values of the overflow-guard half-shifts. NOT trusted axioms:
// Qed proves each by constant folding. Stated as lemmas so the equations
// also exist where the guard `x <= msk >> opsz/2` appears with a ground
// shift the provers cannot otherwise evaluate — folding it to the literal
// 2^(w/2)-1 bound is what lets the mask-concrete mul_bound_* axioms fire.
/*@
lemma half_mask_u32: (0xFFFFFFFF >> 16) == 0xFFFF;
lemma half_mask_u64: (0xFFFFFFFFFFFFFFFF >> 32) == 0xFFFFFFFF;
lemma half_mask_s32: (0x7FFFFFFF >> 16) == 0x7FFF;
lemma half_mask_s64: (0x7FFFFFFFFFFFFFFF >> 32) == 0x7FFFFFFF;
*/

#endif /* AXIOMS_MUL_H */
