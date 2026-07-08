#include "eval_apply_mask.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
  lemma land_comm:
    \forall integer x, y; (x & y) == (y & x);
*/

/*
 * WP's Cbits theory only knows `x & -1 == x` for the *mathematical*
 * integer -1 (axiom land_1bis) and has no bit-level extensionality
 * axiom, so the 64-bit variant `x & 0xFFFFFFFFFFFFFFFF == x` is not a
 * first-order consequence of the shipped axioms and no SMT solver can
 * derive it. We supply it as a trusted axiom: masking with all 64 bits
 * set is the identity on values in [0, 2^64 - 1]. (This is the same
 * fact as land_1bis restricted to 64-bit unsigned values; it is
 * provable from land_extraction + bit extensionality in WP's Coq
 * model, just not in the first-order SMT encoding.)
 */
/*@
  axiomatic LandUint64AllOnes {
    axiom land_uint64_max:
      \forall integer x;
        0 <= x <= 0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x;
  }

  axiomatic LandUint32AllOnes {
    axiom land_uint32_max:
      \forall integer x;
        0 <= x <= 0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x;
  }

*/

/*
 * Same story for monotonicity: Cbits has no bounds axiom for land, so
 * `(x & y) <= x` for non-negative x, y (AND can only clear bits) is
 * also unprovable by SMT. Trusted axiom, again true in the intended
 * bitwise model.
 */
/*@
  axiomatic LandBounds {
    axiom land_nonneg_le:
      \forall integer x, y;
        0 <= x && 0 <= y ==> 0 <= (x & y) <= x;
  }
*/

/*@
	requires rv->u.min <= rv->u.max;
	requires rv->s.min <= rv->s.max;
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->mask;
	ensures mask == _64_BIT_MASK ==> rv->u.min == \old(rv->u.min);
	ensures mask == _64_BIT_MASK ==> rv->u.max == \old(rv->u.max);
	ensures mask == _32_BIT_MASK && (\old(rv->u.min) > mask || \old(rv->u.max) > mask)
	 	==> rv->u.min == 0 && rv->u.max == mask;
	ensures mask == _32_BIT_MASK && (\old(rv->u.min) <= mask && \old(rv->u.max) <= mask)
	 	==> rv->u.min == \old(rv->u.min) && rv->u.max == \old(rv->u.max);
	ensures rv->mask == mask;
	ensures mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN || rv->s.min == \old(rv->s.min);
	ensures mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX || rv->s.max == \old(rv->s.max);
	ensures mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN || rv->s.min == \old(rv->s.min);
	ensures mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX || rv->s.max == \old(rv->s.max);
	ensures rv->v == \old(rv->v);
	ensures rv->u.min <= rv->u.max;
	ensures mask == _64_BIT_MASK ==> rv->s.min <= rv->s.max;
	ensures mask == _32_BIT_MASK ==> rv->s.min <= rv->s.max;
*/
void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask)
{
	struct bpf_reg_val rt;

	rt.u.min = rv->u.min & mask;
	rt.u.max = rv->u.max & mask;

	if (rt.u.min != rv->u.min || rt.u.max != rv->u.max) {
		rv->u.max = RTE_MAX(rt.u.max, mask);
		rv->u.min = 0;
	}

	eval_smax_bound(&rt, mask);

	// Proposed fix: comment L94 & L95 and uncomment L87-91
	// if (rv->s.min < rt.s.min || rv->s.max > rt.s.max) {
	// 	/* signed range escapes the width → low bits unknown → widen */
	// 	rv->s.min = rt.s.min;              // INT_MIN_w
	// 	rv->s.max = rt.s.max;              // INT_MAX_w
	// }
	// /* else: already inside the width; truncation is the identity → leave it */

	rv->s.max = RTE_MIN(rt.s.max, rv->s.max);
	rv->s.min = RTE_MAX(rt.s.min, rv->s.min);

	rv->mask = mask;
}


