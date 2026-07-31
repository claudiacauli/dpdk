#include "eval_mul.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

#include "axioms_mul.h"
#include "../../common/axioms_and.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	assigns \nothing;
	ensures \result == ((a * b) & msk);
*/
static uint64_t mul_umask(uint64_t a, uint64_t b, uint64_t msk)
{
	return (a * b) & msk;
}

#ifdef FIX_MUL_SCONST

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t mul_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	assigns \nothing;
	ensures \result == to_signed((d * e) & msk, msk);
*/
static int64_t mul_sext2(int64_t d, int64_t e, uint64_t msk)
{
	return mul_sext(((uint64_t)d * (uint64_t)e) & msk, msk);
}
#endif

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
	ensures usound:     eval_mul_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_mul_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

#ifdef PROVE_OPTIMALITY
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.max) <= (msk >> (opsz / 2)) &&
		\old(rs->u.max) <= (msk >> (opsz / 2))
			==> eval_mul_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->s.min) >= 0 && \old(rs->s.min) >= 0 &&
		\old(rd->s.max) <= ((msk >> 1) >> (opsz / 2)) &&
		\old(rs->s.max) <= ((msk >> 1) >> (opsz / 2))
			==> eval_mul_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
#endif
*/
void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{

	/*@ assert ob32: msk == 0xFFFFFFFF ==> opsz == 32; */
	/*@ assert ob64: msk == 0xFFFFFFFFFFFFFFFF ==> opsz == 64; */

	/*@ assert msk_shape: (msk & (msk + 1)) == 0; */

	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		rd->u.min = mul_umask(rd->u.min, rs->u.min, msk);
		rd->u.max = mul_umask(rd->u.max, rs->u.max, msk);
#ifdef FIX_MUL_UGUARD

	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz / 2) {
#else
	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz) {
#endif

		/*@ assert u_nof32: msk == 0xFFFFFFFF ==>
		      (rd->u.max * rs->u.max) <= msk; */
		/*@ assert u_nof64: msk == 0xFFFFFFFFFFFFFFFF ==>
		      (rd->u.max * rs->u.max) <= msk; */
		/*@ assert u_mono: (rd->u.min * rs->u.min) <= (rd->u.max * rs->u.max); */
		rd->u.max *= rs->u.max;
		rd->u.min *= rs->u.min;

		/*@ assert usound_link_umax:
		      rd->u.max == \at(rd->u.max,Pre) * \at(rs->u.max,Pre); */
		/*@ assert usound_link_umin:
		      rd->u.min == \at(rd->u.min,Pre) * \at(rs->u.min,Pre); */
		/*@ assert usound_link_corner:
		      (\at(rd->u.max,Pre) * \at(rs->u.max,Pre)) <= msk; */
	} else
		eval_umax_bound(rd, msk);

	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
#ifdef FIX_MUL_SCONST

		rd->s.min = mul_sext2(rd->s.min, rs->s.min, msk);
		rd->s.max = mul_sext2(rd->s.max, rs->s.max, msk);
#else
		rd->s.min = ((uint64_t)rd->s.min * (uint64_t)rs->s.min) & msk;
		rd->s.max = ((uint64_t)rd->s.max * (uint64_t)rs->s.max) & msk;
#endif
#ifdef FIX_MUL_SGUARD

	} else if (rd->s.min >= 0 && rs->s.min >= 0 &&
			rd->s.max <= (msk >> 1) >> (opsz / 2) &&
			rs->s.max <= (msk >> 1) >> (opsz / 2)) {
#else
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
#endif
		/*@ assert s_nof32: msk == 0xFFFFFFFF ==>
		      (rd->s.max * rs->s.max) <= (msk >> 1); */
		/*@ assert s_nof64: msk == 0xFFFFFFFFFFFFFFFF ==>
		      (rd->s.max * rs->s.max) <= (msk >> 1); */
		/*@ assert s_mono: (rd->s.min * rs->s.min) <= (rd->s.max * rs->s.max); */
		rd->s.max *= rs->s.max;

		/*@ assert s_frame: rs->s.min == \at(rs->s.min, Pre); */
		rd->s.min *= rs->s.min;

		/*@ assert ssound_link_smax:
		      rd->s.max == \at(rd->s.max,Pre) * \at(rs->s.max,Pre); */
		/*@ assert ssound_link_smin:
		      rd->s.min == \at(rd->s.min,Pre) * \at(rs->s.min,Pre); */
		/*@ assert ssound_link_corner:
		      (\at(rd->s.max,Pre) * \at(rs->s.max,Pre)) <= (msk >> 1); */
	} else
		eval_smax_bound(rd, msk);

#ifdef PROVE_OPTIMALITY

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.max,Pre) <= (msk >> (opsz / 2)) &&
	      \at(rs->u.max,Pre) <= (msk >> (opsz / 2)) ==>
	        ((\at(rd->u.max,Pre) * \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.max,Pre) <= (msk >> (opsz / 2)) &&
	      \at(rs->u.max,Pre) <= (msk >> (opsz / 2)) ==>
	        ((\at(rd->u.min,Pre) * \at(rs->u.min,Pre)) & msk) == rd->u.min; */

	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.max,Pre)) & msk, msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.min,Pre)) & msk, msk); */

	/*@ assert sopt_pat_id:
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.max,Pre)) & msk) == \at(rd->s.max,Pre) &&
	        (((uint64_t)\at(rs->s.max,Pre)) & msk) == \at(rs->s.max,Pre); */

	/*@ assert sopt_sum_smax32:
	      msk == 0xFFFFFFFF &&
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smax64:
	      msk == 0xFFFFFFFFFFFFFFFF &&
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin:
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
#endif
}
