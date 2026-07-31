#include "eval_arsh.h"
#include "lemmas_canon_arsh.h"
#include "../eval_max_bound/eval_max_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	requires \separated(rd, rs);
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
	ensures usound:     eval_arsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_arsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk)
			==> eval_arsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) &&
		(\old(rd->u.min) > (msk >> 1) || \old(rd->u.max) <= (msk >> 1))
			==> eval_arsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_arsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	uint32_t shv;

	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		return;
	}

#ifdef FIX_ARSH_UNSIGNED_SIGN

	{
		uint64_t half = msk >> 1;
		if (rd->u.min > half) {
			int64_t vmin = (opsz == 32) ?
				(int32_t)(uint32_t)rd->u.min : (int64_t)rd->u.min;
			int64_t vmax = (opsz == 32) ?
				(int32_t)(uint32_t)rd->u.max : (int64_t)rd->u.max;

			/*@ check uopt_sext_min:
			      vmin == to_signed(\at(rd->u.min,Pre), msk); */
			/*@ check uopt_sext_max:
			      vmax == to_signed(\at(rd->u.max,Pre), msk); */
			rd->u.min = ((uint64_t)(vmin >> rs->u.min)) & msk;
			rd->u.max = ((uint64_t)(vmax >> rs->u.max)) & msk;

			/*@ check uopt_sum_neg_umax:
			      (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk) == rd->u.max; */
			/*@ check uopt_sum_neg_umin:
			      (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk) == rd->u.min; */

			/*@ assert usound_link_neg_umax:
			      rd->u.max == (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk); */
			/*@ assert usound_link_neg_umin:
			      rd->u.min == (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk); */
		} else if (rd->u.max > half) {
			rd->u.min = 0;
			rd->u.max = msk;
		} else {
			rd->u.max >>= rs->u.min;
			rd->u.min >>= rs->u.max;

			/*@ check uopt_sum_pos_umax:
			      (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk) == rd->u.max; */
			/*@ check uopt_sum_pos_umin:
			      (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk) == rd->u.min; */
		}
	}
#else
	rd->u.max = (int64_t)rd->u.max >> rs->u.min;
	rd->u.min = (int64_t)rd->u.min >> rs->u.max;
#endif

	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
	#ifdef FIX_ARSH_32EXT_SHL

		rd->s.min = (int64_t)((uint64_t)rd->s.min << opsz);
		rd->s.max = (int64_t)((uint64_t)rd->s.max << opsz);
	#else
		rd->s.min <<= opsz;
		rd->s.max <<= opsz;
	#endif
		shv = opsz;
	} else
		shv = 0;

	if (rd->s.min < 0)
		rd->s.min = (rd->s.min >> (rs->u.min + shv)) & msk;
	else
		rd->s.min = (rd->s.min >> (rs->u.max + shv)) & msk;

	if (rd->s.max < 0)
		rd->s.max = (rd->s.max >> (rs->u.max + shv)) & msk;
	else
		rd->s.max = (rd->s.max >> (rs->u.min + shv)) & msk;

#ifdef FIX_ARSH_SIGNED_MASK

	if (msk == _32_BIT_MASK) {
		rd->s.min = (int32_t)(uint32_t)rd->s.min;
		rd->s.max = (int32_t)(uint32_t)rd->s.max;
	}

	/*@ assert smax_shift_id:
	      rd->s.max == (\at(rd->s.max, Pre) < 0
	                    ? \at(rd->s.max, Pre) >> \at(rs->u.max, Pre)
	                    : \at(rd->s.max, Pre) >> \at(rs->u.min, Pre)); */
	/*@ assert smin_shift_id:
	      rd->s.min == (\at(rd->s.min, Pre) < 0
	                    ? \at(rd->s.min, Pre) >> \at(rs->u.min, Pre)
	                    : \at(rd->s.min, Pre) >> \at(rs->u.max, Pre)); */

	/*@ check sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    (\at(rd->s.max,Pre) < 0 ? \at(rs->u.max,Pre)
	                                            : \at(rs->u.min,Pre)), msk); */
	/*@ check sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    (\at(rd->s.min,Pre) < 0 ? \at(rs->u.min,Pre)
	                                            : \at(rs->u.max,Pre)), msk); */
	/*@ check sopt_sum_smax:
	      (to_signed(((uint64_t)\at(rd->s.max,Pre)) & msk, msk)
	       >> (\at(rd->s.max,Pre) < 0 ? \at(rs->u.max,Pre)
	                                  : \at(rs->u.min,Pre))) == rd->s.max; */
	/*@ check sopt_sum_smin:
	      (to_signed(((uint64_t)\at(rd->s.min,Pre)) & msk, msk)
	       >> (\at(rd->s.min,Pre) < 0 ? \at(rs->u.min,Pre)
	                                  : \at(rs->u.max,Pre))) == rd->s.min; */
#endif

	/*@ check uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre), \at(rd->u.max,Pre),
	                    (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.max,Pre)
	                                                     : \at(rs->u.min,Pre)),
	                    msk); */
	/*@ check uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre), \at(rd->u.min,Pre),
	                    (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.min,Pre)
	                                                     : \at(rs->u.max,Pre)),
	                    msk); */
	/*@ check uopt_sum_end_umax:
	      (\at(rd->u.min,Pre) > (msk >> 1) ||
	       \at(rd->u.max,Pre) <= (msk >> 1)) ==>
	        (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
	           >> (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.max,Pre)
	                                               : \at(rs->u.min,Pre))))
	         & msk) == rd->u.max; */
	/*@ check uopt_sum_end_umin:
	      (\at(rd->u.min,Pre) > (msk >> 1) ||
	       \at(rd->u.max,Pre) <= (msk >> 1)) ==>
	        (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
	           >> (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.min,Pre)
	                                               : \at(rs->u.max,Pre))))
	         & msk) == rd->u.min; */
}
