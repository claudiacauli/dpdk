#include "eval_sub.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"
#include "../../common/axioms_sub.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_sub_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_sub_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->u.min) < \old(rs->u.max)) <==>
		 (\old(rd->u.max) < \old(rs->u.min)))
			==> eval_sub_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->s.min) - \old(rs->s.max) < -(int64_t)(msk >> 1) - 1) <==>
		 (\old(rd->s.max) - \old(rs->s.min) < -(int64_t)(msk >> 1) - 1)) &&
		((\old(rd->s.min) - \old(rs->s.max) > (int64_t)(msk >> 1)) <==>
		 (\old(rd->s.max) - \old(rs->s.min) > (int64_t)(msk >> 1)))
			==> eval_sub_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_sub(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)
{
	struct bpf_reg_val rv;

	rv.u.min = (rd->u.min - rs->u.max) & msk;
	rv.u.max = (rd->u.max - rs->u.min) & msk;

	/*@ assert uopt_nowrap:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre)); */
#ifdef FIX_SUB_UNSIGNED_OVFL

	/*@ assert uopt_nowrap_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1 &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1); */
#endif
	rv.s.min = ((uint64_t)rd->s.min - (uint64_t)rs->s.max) & msk;
	rv.s.max = ((uint64_t)rd->s.max - (uint64_t)rs->s.min) & msk;

	#ifdef FIX_SUB_SIGNED_32

		if (msk == _32_BIT_MASK) {

			/*@ assert mask32_min_rng: 0 <= rv.s.min <= 0xFFFFFFFF; */
			/*@ assert mask32_max_rng: 0 <= rv.s.max <= 0xFFFFFFFF; */
			/*@ assert mask32_min:
			      rv.s.min == rd->s.min - rs->s.max ||
			      rv.s.min == rd->s.min - rs->s.max + 0x100000000; */
			/*@ assert mask32_max:
			      rv.s.max == rd->s.max - rs->s.min ||
			      rv.s.max == rd->s.max - rs->s.min + 0x100000000; */
			rv.s.min = (int32_t)(uint32_t)rv.s.min;
			rv.s.max = (int32_t)(uint32_t)rv.s.max;
			/*@ assert sext32_min_rng: INT32_MIN <= rv.s.min <= INT32_MAX; */
			/*@ assert sext32_max_rng: INT32_MIN <= rv.s.max <= INT32_MAX; */
			/*@ assert sext32_min_val:
			      rv.s.min == rd->s.min - rs->s.max ||
			      rv.s.min == rd->s.min - rs->s.max - 0x100000000 ||
			      rv.s.min == rd->s.min - rs->s.max + 0x100000000; */
			/*@ assert sext32_max_val:
			      rv.s.max == rd->s.max - rs->s.min ||
			      rv.s.max == rd->s.max - rs->s.min - 0x100000000 ||
			      rv.s.max == rd->s.max - rs->s.min + 0x100000000; */
		}
	#endif

	/*@ assert sopt_nowrap_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre); */
	/*@ assert sopt_nowrap_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre); */
#ifdef FIX_SUB_SIGNED_OVFL_OPT

	/*@ assert sopt_of_signs:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        0 <= \at(rd->s.min,Pre) && \at(rs->s.max,Pre) < 0; */
	/*@ assert sopt_uf_signs:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        \at(rd->s.max,Pre) < 0 && 0 < \at(rs->s.min,Pre); */
	/*@ assert sext64_min_val: msk == _64_BIT_MASK ==>
	      (rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) ||
	       rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - 0x10000000000000000 ||
	       rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + 0x10000000000000000); */
	/*@ assert sext64_max_val: msk == _64_BIT_MASK ==>
	      (rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) ||
	       rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - 0x10000000000000000 ||
	       rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + 0x10000000000000000); */

	/*@ assert sopt_ofwrap_min:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_ofwrap_max:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_ufwrap_min:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + msk + 1; */
	/*@ assert sopt_ufwrap_max:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + msk + 1; */
#endif

#ifdef FIX_SUB_UNSIGNED_OVFL

	if ((rv.u.min > rd->u.min) != (rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);
#else
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min > rd->u.min || rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);
#endif

	/*@ assert uopt_nowiden:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre)); */
#ifdef FIX_SUB_UNSIGNED_OVFL
	/*@ assert uopt_nowiden_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1 &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1); */
#endif

#if defined(FIX_SUB_SIGNED_OVFL_OPT)

	{
		int uf_min = (rs->s.max >= 0 && rv.s.min > rd->s.min);
		int of_min = (rs->s.max < 0 && rv.s.min < rd->s.min);
		int uf_max = (rs->s.min >= 0 && rv.s.max > rd->s.max);
		int of_max = (rs->s.min < 0 && rv.s.max < rd->s.max);
		if (uf_min != uf_max || of_min != of_max)
			eval_smax_bound(&rv, msk);
	}
#elif defined(FIX_SUB_SIGNED_OVFL)

	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.max < 0 && rv.s.min < rd->s.min) ||
			(rs->s.max >= 0 && rv.s.min > rd->s.min)) ||
			((rs->s.min < 0 && rv.s.max < rd->s.max) ||
			(rs->s.min >= 0 && rv.s.max > rd->s.max))))
		eval_smax_bound(&rv, msk);
#else
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.max < 0 && rv.s.min < rd->s.min) ||
			rv.s.min > rd->s.min) ||
			((rs->s.min < 0 && rv.s.max < rd->s.max) ||
			rv.s.max > rd->s.max)))
		eval_smax_bound(&rv, msk);
#endif

	/*@ assert uopt_sum_rv_max:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre); */
	/*@ assert uopt_sum_rv_min:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre); */
	/*@ assert sopt_sum_rv_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre); */
	/*@ assert sopt_sum_rv_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre); */
#ifdef FIX_SUB_UNSIGNED_OVFL
	/*@ assert uopt_sum_rv_max_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1; */
	/*@ assert uopt_sum_rv_min_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1; */
#endif
#ifdef FIX_SUB_SIGNED_OVFL_OPT

	/*@ assert sopt_sum_rv_min_of:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_max_of:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_min_uf:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + msk + 1; */
	/*@ assert sopt_sum_rv_max_uf:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + msk + 1; */
#endif

	rd->s = rv.s;
	rd->u = rv.u;

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        ((\at(rd->u.max,Pre) - \at(rs->u.min,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        ((\at(rd->u.min,Pre) - \at(rs->u.max,Pre)) & msk) == rd->u.min; */
#ifdef FIX_SUB_UNSIGNED_OVFL

	/*@ assert uopt_sum_umax_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        ((\at(rd->u.max,Pre) - \at(rs->u.min,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        ((\at(rd->u.min,Pre) - \at(rs->u.max,Pre)) & msk) == rd->u.min; */
#endif
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.min,Pre)) & msk, msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.max,Pre)) & msk, msk); */
}
