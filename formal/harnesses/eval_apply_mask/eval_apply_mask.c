#include "eval_apply_mask.h"
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
	ensures smin32:     mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN || rv->s.min == \old(rv->s.min);
	ensures smax32:     mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX || rv->s.max == \old(rv->s.max);
	ensures smin64:     mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN || rv->s.min == \old(rv->s.min);
	ensures smax64:     mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX || rv->s.max == \old(rv->s.max);
	ensures frame_v:    rv->v == \old(rv->v);
	ensures ord64:      mask == _64_BIT_MASK ==> range_ordering(rv);
	ensures ord32:      mask == _32_BIT_MASK ==> range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
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
}


