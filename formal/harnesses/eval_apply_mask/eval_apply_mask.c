#include "eval_apply_mask.h"

#include "../../common/lemmas_canon.h"

#include "axioms_apply_mask.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	requires range_ordering(rv);
	requires own_width: (rv->mask == _32_BIT_MASK ||
			rv->mask == _64_BIT_MASK) &&
		unsigned_range_within_width(rv, rv->mask);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->mask;

	ensures umin64:     mask == _64_BIT_MASK ==> rv->u.min == \old(rv->u.min);
	ensures umax64:     mask == _64_BIT_MASK ==> rv->u.max == \old(rv->u.max);
	ensures uwiden32:   mask == _32_BIT_MASK &&
		\old(rv->u.min) / (mask + 1) != \old(rv->u.max) / (mask + 1)
	 	==> rv->u.min == 0 && rv->u.max == mask;
	ensures ukeep32:    mask == _32_BIT_MASK &&
		\old(rv->u.min) / (mask + 1) == \old(rv->u.max) / (mask + 1)
	 	==> rv->u.min == (\old(rv->u.min) & mask) && rv->u.max == (\old(rv->u.max) & mask);
	ensures mask_set:   rv->mask == mask;
	ensures mask_ok:    rv->mask == _32_BIT_MASK || rv->mask == _64_BIT_MASK;
	ensures smin32:     mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN || rv->s.min == \old(rv->s.min);
	ensures smax32:     mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX || rv->s.max == \old(rv->s.max);
	ensures smin64:     mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN ||
		rv->s.min == \old(rv->s.min) || rv->s.min == rv->u.min;
	ensures smax64:     mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX ||
		rv->s.max == \old(rv->s.max) || rv->s.max == rv->u.max;
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

#ifdef PROVE_OPTIMALITY
	ensures uopt: eval_apply_mask_unsigned_optimal(\old(*rv), *rv, mask);
	ensures sopt: \old(signed_range_within_width(rv, mask)) &&
			mask <= \old(rv->mask)
			==> eval_apply_mask_signed_optimal(\old(*rv), *rv, mask);
#endif
*/
void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask)
{
	struct bpf_reg_val rt;

	/*@ assert blk_div_min: mask == _32_BIT_MASK ==>
	      (rv->u.min & 0xFFFFFFFF00000000) ==
	      0x100000000 * (rv->u.min / 0x100000000); */
	/*@ assert blk_div_max: mask == _32_BIT_MASK ==>
	      (rv->u.max & 0xFFFFFFFF00000000) ==
	      0x100000000 * (rv->u.max / 0x100000000); */

	rt.u.min = rv->u.min & mask;
	rt.u.max = rv->u.max & mask;

#ifdef FIX_APPLY_MASK_OPT

	if ((rv->u.min & ~mask) != (rv->u.max & ~mask)) {
		rv->u.min = 0;
		rv->u.max = mask;
	} else {
		rv->u.min = rt.u.min;
		rv->u.max = rt.u.max;
	}
#else
	if (rt.u.min != rv->u.min || rt.u.max != rv->u.max) {
		rv->u.max = RTE_MAX(rt.u.max, mask);
		rv->u.min = 0;
	}
#endif

	eval_smax_bound(&rt, mask);

#ifdef FIX_APPLY_MASK_CONSIST

	if (mask > rv->mask) {
		rv->s.min = (int64_t)rv->u.min;
		rv->s.max = (int64_t)rv->u.max;
	} else
#endif
	#ifdef FIX_APPLY_MASK_SIGNED
		if (rv->s.min < rt.s.min || rv->s.max > rt.s.max) {
			rv->s.min = rt.s.min;
			rv->s.max = rt.s.max;
		}
	#else
		{
			rv->s.max = RTE_MIN(rt.s.max, rv->s.max);
			rv->s.min = RTE_MAX(rt.s.min, rv->s.min);
		}
	#endif

	rv->mask = mask;

	/*@ check uopt_id_min:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.min,Pre) & mask) == \at(rv->u.min,Pre); */
	/*@ check uopt_id_max:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.max,Pre) & mask) == \at(rv->u.max,Pre); */
	/*@ check uopt_keep:
	      \at(rv->u.max,Pre) <= mask ==>
	        rv->u.min == \at(rv->u.min,Pre) && rv->u.max == \at(rv->u.max,Pre); */
#ifdef FIX_APPLY_MASK_OPT

	/*@ assert uopt_keep_blk: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) ==
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        rv->u.min == (\at(rv->u.min,Pre) & mask) &&
	        rv->u.max == (\at(rv->u.max,Pre) & mask); */

	/*@ assert uopt_str_out: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        rv->u.min == 0 && rv->u.max == mask; */
	/*@ assert uopt_str_zero: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        \at(rv->u.min,Pre) <= (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) <=
	        \at(rv->u.max,Pre) &&
	        ((\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) & mask) == 0; */
	/*@ assert uopt_str_top: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        \at(rv->u.min,Pre) <= (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) - 1 &&
	        (((\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) - 1) & mask) == mask; */
#endif

	/*@ assert sopt_keep:
	      \at(signed_range_within_width(rv, mask),Pre) &&
	      mask <= \at(rv->mask,Pre) ==>
	        rv->s.min == \at(rv->s.min,Pre) && rv->s.max == \at(rv->s.max,Pre); */
#ifdef FIX_APPLY_MASK_CONSIST

	/*@ assert sopt_widen:
	      mask > \at(rv->mask,Pre) ==>
	        rv->s.min == rv->u.min && rv->s.max == rv->u.max &&
	        0 <= rv->u.min && rv->u.max <= (mask >> 1); */
#endif
	/*@ assert sopt_rt_max:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.max,Pre)) & mask, mask)
	          == \at(rv->s.max,Pre); */
	/*@ assert sopt_rt_min:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.min,Pre)) & mask, mask)
	          == \at(rv->s.min,Pre); */
}
