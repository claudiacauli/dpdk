#include "eval_lsh.h"
#include "../../common/axioms_shift_opt.h"

#include "lemmas_canon_lsh.h"
#include "../eval_max_bound/eval_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

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
	ensures usound:     eval_lsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_lsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) &&
		\old(rd->u.max) <= (msk >> \old(rs->u.max))
			==> eval_lsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) <= op_bits(msk) - 2 &&
		\old(rd->s.min) >= 0 &&
		\old(rd->s.max) < ((msk >> 1) >> \old(rs->u.max))
			==> eval_lsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_lsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		/*@ assert full_slo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert full_shi: rd->s.max == (int64_t)(msk >> 1); */
		return;
	}

	if (rd->u.max > RTE_LEN2MASK(opsz - rs->u.max, uint64_t))
		eval_umax_bound(rd, msk);
	else {
		/*@ assert in_ord_d: rd->u.min <= rd->u.max; */
		/*@ assert in_ord_s: rs->u.min <= rs->u.max; */
		/*@ assert min_fits: rd->u.min <= RTE_LEN2MASK(opsz - rs->u.min, uint64_t); */

		/*@ assert max_fits: rd->u.max <= RTE_LEN2MASK(opsz - rs->u.max, uint64_t); */
		/*@ assert max_shift_fits: (rd->u.max << rs->u.max) <= msk; */
		rd->u.max <<= rs->u.max;
		rd->u.min <<= rs->u.min;
		/*@ assert umin_stone: rd->u.min <= msk; */
		/*@ assert uwidth_stone: rd->u.max <= msk; */

		/*@ assert uopt_sum_umax:
		      ((\at(rd->u.max,Pre) << \at(rs->u.max,Pre)) & msk) == rd->u.max; */
		/*@ assert uopt_sum_umin:
		      ((\at(rd->u.min,Pre) << \at(rs->u.min,Pre)) & msk) == rd->u.min; */
	}

	if ((uint64_t)rd->s.min >> (opsz - 1) != 0 || rd->s.max >=
			(rs->u.max == opsz - 1 ? 0 :
				 RTE_LEN2MASK(opsz - rs->u.max - 1, int64_t))) {
		eval_smax_bound(rd, msk);
		/*@ assert sfull_lo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert sfull_hi: rd->s.max == (int64_t)(msk >> 1); */
	}
	else {
		/*@ assert s_in_ord: rd->s.min <= rd->s.max; */
		/*@ assert sq_ord: rs->u.min <= rs->u.max; */
		/*@ assert smin_nonneg: 0 <= rd->s.min; */
		rd->s.max <<= rs->u.max;
		rd->s.min <<= rs->u.min;
		/*@ assert swidth_stone: rd->s.max <= (int64_t)(msk >> 1); */

		/*@ assert ssound_link_smax:
		      (\at(rd->s.max,Pre) << \at(rs->u.max,Pre)) <= (msk >> 1); */
		/*@ assert smax_shift_id:
		      rd->s.max == \at(rd->s.max, Pre) << \at(rs->u.max, Pre); */
		/*@ assert smin_shift_id:
		      rd->s.min == \at(rd->s.min, Pre) << \at(rs->u.min, Pre); */
		/*@ assert sopt_sum_smax:
		      to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk)
		                 << \at(rs->u.max,Pre)) & msk, msk) == rd->s.max; */
		/*@ assert sopt_sum_smin:
		      to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk)
		                 << \at(rs->u.min,Pre)) & msk, msk) == rd->s.min; */
	}

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    \at(rs->u.max,Pre), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    \at(rs->u.min,Pre), msk); */

	/*@ assert uopt_branch_sel:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        RTE_LEN2MASK(opsz - \at(rs->u.max,Pre), uint64_t)
	          == (msk >> \at(rs->u.max,Pre)); */
	/*@ assert sopt_branch_sel_sign:
	      \at(rd->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.min,Pre)) >> (opsz - 1)) == 0; */
	/*@ assert sopt_branch_sel_thr:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 ==>
	        RTE_LEN2MASK(opsz - \at(rs->u.max,Pre) - 1, int64_t)
	          == ((msk >> 1) >> \at(rs->u.max,Pre)); */

	/*@ assert uopt_sum_end_umax:
	      \at(rs->u.max,Pre) < op_bits(msk) &&
	      \at(rd->u.max,Pre) <= (msk >> \at(rs->u.max,Pre)) ==>
	        ((\at(rd->u.max,Pre) << \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_end_umin:
	      \at(rs->u.max,Pre) < op_bits(msk) &&
	      \at(rd->u.max,Pre) <= (msk >> \at(rs->u.max,Pre)) ==>
	        ((\at(rd->u.min,Pre) << \at(rs->u.min,Pre)) & msk) == rd->u.min; */
	/*@ assert sopt_sum_end_smax:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 &&
	      \at(rd->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) < ((msk >> 1) >> \at(rs->u.max,Pre)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk)
	                   << \at(rs->u.max,Pre)) & msk, msk) == rd->s.max; */
	/*@ assert sopt_sum_end_smin:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 &&
	      \at(rd->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) < ((msk >> 1) >> \at(rs->u.max,Pre)) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk)
	                   << \at(rs->u.min,Pre)) & msk, msk) == rd->s.min; */
}
