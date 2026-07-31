#include "eval_rsh.h"
#include "../../common/axioms_shift_opt.h"

#include "../../common/lemmas_canon.h"
#include "../eval_max_bound/eval_max_bound.h"
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
	ensures usound:     eval_rsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_rsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk)
			==> eval_rsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) && \old(rd->s.min) >= 0
			==> eval_rsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_rsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		/*@ assert full_slo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert full_shi: rd->s.max == (int64_t)(msk >> 1); */
		return;
	}

	/*@ assert in_ord_d: rd->u.min <= rd->u.max; */
	/*@ assert in_ord_s: rs->u.min <= rs->u.max; */
	rd->u.max >>= rs->u.min;
	rd->u.min >>= rs->u.max;

	if ((uint64_t)rd->s.min >> (opsz - 1) != 0) {
		eval_smax_bound(rd, msk);
		/*@ assert sfull_lo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert sfull_hi: rd->s.max == (int64_t)(msk >> 1); */
	}
	else {
		/*@ assert s_in_ord: rd->s.min <= rd->s.max; */
		/*@ assert smin_nonneg: 0 <= rd->s.min; */
		rd->s.max >>= rs->u.min;
		rd->s.min >>= rs->u.max;
		/*@ assert smax_shift_id:
		      rd->s.max == \at(rd->s.max, Pre) >> \at(rs->u.min, Pre); */
		/*@ assert smin_shift_id:
		      rd->s.min == \at(rd->s.min, Pre) >> \at(rs->u.max, Pre); */
		/*@ assert sopt_sum_smax:
		      \at(rd->s.min,Pre) >= 0 ==>
		        to_signed((((uint64_t)\at(rd->s.max,Pre)) & msk)
		                  >> \at(rs->u.min,Pre), msk) == rd->s.max; */
		/*@ assert sopt_sum_smin:
		      \at(rd->s.min,Pre) >= 0 ==>
		        to_signed((((uint64_t)\at(rd->s.min,Pre)) & msk)
		                  >> \at(rs->u.max,Pre), msk) == rd->s.min; */
	}

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        (\at(rd->u.max,Pre) >> \at(rs->u.min,Pre)) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        (\at(rd->u.min,Pre) >> \at(rs->u.max,Pre)) == rd->u.min; */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    \at(rs->u.min,Pre), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    \at(rs->u.max,Pre), msk); */

	/*@ assert sopt_branch_sel:
	      \at(rd->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.min,Pre)) >> (opsz - 1)) == 0; */

	/*@ assert sopt_sum_end_smax:
	      \at(rd->s.min,Pre) >= 0 ==>
	        to_signed((((uint64_t)\at(rd->s.max,Pre)) & msk)
	                  >> \at(rs->u.min,Pre), msk) == rd->s.max; */
	/*@ assert sopt_sum_end_smin:
	      \at(rd->s.min,Pre) >= 0 ==>
	        to_signed((((uint64_t)\at(rd->s.min,Pre)) & msk)
	                  >> \at(rs->u.max,Pre), msk) == rd->s.min; */
}
