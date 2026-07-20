#include "eval_apply_mask.h"
/* to_signed_canon_rt: the sopt witness is the canonical endpoint itself, and
 * the predicate re-encodes it as a pattern before decoding, so the chain has
 * to cross representations exactly once. See common/lemmas_canon.h. */
#include "../../common/lemmas_canon.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	requires range_ordering(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->mask;

	ensures umin64:     mask == _64_BIT_MASK ==> rv->u.min == \old(rv->u.min);
	ensures umax64:     mask == _64_BIT_MASK ==> rv->u.max == \old(rv->u.max);
	ensures uwiden32:   mask == _32_BIT_MASK && (\old(rv->u.min) > mask || \old(rv->u.max) > mask)
	 	==> rv->u.min == 0 && rv->u.max == mask;
	ensures ukeep32:    mask == _32_BIT_MASK && (\old(rv->u.min) <= mask && \old(rv->u.max) <= mask)
	 	==> rv->u.min == \old(rv->u.min) && rv->u.max == \old(rv->u.max);
	ensures mask_set:   rv->mask == mask;
	ensures mask_ok:    rv->mask == _32_BIT_MASK || rv->mask == _64_BIT_MASK;
	ensures smin32:     mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN || rv->s.min == \old(rv->s.min);
	ensures smax32:     mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX || rv->s.max == \old(rv->s.max);
	ensures smin64:     mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN || rv->s.min == \old(rv->s.min);
	ensures smax64:     mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX || rv->s.max == \old(rv->s.max);
	ensures unchanged_v:    rv->v == \old(rv->v);
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
	ensures agree_min: \old(range_agreement(rv, mask)) &&
			\old(range_within_width(rv, mask))
			==> min_agreement(rv, mask);
	ensures agree_max: \old(range_agreement(rv, mask)) &&
			\old(range_within_width(rv, mask))
			==> max_agreement(rv, mask);
	ensures usound:     eval_apply_mask_unsigned_soundness(\old(*rv), *rv, mask);
	ensures ssound:     eval_apply_mask_signed_soundness(\old(*rv), *rv, mask);

	// OP-OPTIMALITY (apply_mask-optimal). PER-TRACK, mirroring the per-track
	// soundness above -- and note what that buys: unlike every binary operator,
	// these predicates quantify the witness over ONE track's range only, with no
	// cross-track un_witness obligation. So apply_mask needs NO self_optimal
	// precondition: the endpoint is its own witness by construction. The guards
	// below are purely "the widening branch did not fire".
	//
	// u track: masking is the identity exactly when the range already fits under
	// the mask; a range STRADDLING a 2^32 boundary widens to [0,mask] and is
	// genuinely loose (u.max == mask is attained only if the masked set spans the
	// low block), so the non-straddle guard is necessary, not incidental. The
	// 64-bit mask fits trivially, which is why one bound covers both widths.
	//
	// s track: eval_smax_bound(&rt) loads rt.s with the width's [INT_MIN, INT_MAX],
	// and the code widens iff rv->s escapes that -- i.e. iff the signed range is
	// not already within width. Hence the guard is exactly
	// signed_range_within_width, which this contract does NOT require up front
	// (see the requires above: only range_ordering).
	ensures uopt: \old(rv->u.max) <= mask
			==> eval_apply_mask_unsigned_optimal(\old(*rv), *rv, mask);
	ensures sopt: \old(signed_range_within_width(rv, mask))
			==> eval_apply_mask_signed_optimal(\old(*rv), *rv, mask);
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

	#ifdef FIX_APPLY_MASK_SIGNED
		/* Fixed */
		if (rv->s.min < rt.s.min || rv->s.max > rt.s.max) {
			/* signed range escapes the width → low bits unknown → widen */
			rv->s.min = rt.s.min;              // INT_MIN_w
			rv->s.max = rt.s.max;              // INT_MAX_w
		}
	#else
		/* Original */
		rv->s.max = RTE_MIN(rt.s.max, rv->s.max);
		rv->s.min = RTE_MAX(rt.s.min, rv->s.min);
	#endif

	rv->mask = mask;

	/*
	 * OP-OPTIMALITY stones. Both tracks reduce to the same shape: under the
	 * guard the widening branch does not fire, the endpoints survive
	 * unchanged, and each endpoint witnesses ITSELF (the per-track predicates
	 * need no cross-track witness, so there is no bin_witness step here).
	 */
	/* u: masking is the identity on a range that already fits, which is what
	 * makes the `rt.u != rv->u` widening test false. */
	/*@ check uopt_id_min:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.min,Pre) & mask) == \at(rv->u.min,Pre); */
	/*@ check uopt_id_max:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.max,Pre) & mask) == \at(rv->u.max,Pre); */
	/*@ check uopt_keep:
	      \at(rv->u.max,Pre) <= mask ==>
	        rv->u.min == \at(rv->u.min,Pre) && rv->u.max == \at(rv->u.max,Pre); */

	/* s: rt.s holds the width's [INT_MIN, INT_MAX] after eval_smax_bound, so a
	 * within-width signed range fails the escape test and is kept; the
	 * re-encode/decode round-trip on a canonical endpoint is the identity
	 * (to_signed_canon_rt). */
	/*@ assert sopt_keep:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        rv->s.min == \at(rv->s.min,Pre) && rv->s.max == \at(rv->s.max,Pre); */
	/*@ assert sopt_rt_max:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.max,Pre)) & mask, mask)
	          == \at(rv->s.max,Pre); */
	/*@ assert sopt_rt_min:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.min,Pre)) & mask, mask)
	          == \at(rv->s.min,Pre); */
}


