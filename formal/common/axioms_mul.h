#ifndef AXIOMS_MUL_H
#define AXIOMS_MUL_H

#include "specs.h"

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
}
*/

#endif /* AXIOMS_MUL_H */
