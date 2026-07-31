#include "eval_neg.h"

#ifdef FIX_NEG_SIGNED_32

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t neg_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}
#endif

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd);
	requires is_scalar(rd->v.type);
	requires range_ordering(rd);
	requires range_within_width(rd, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_neg_unsigned_soundness(\old(*rd), *rd, msk);
	ensures ssound:     eval_neg_signed_soundness(\old(*rd), *rd, msk);

	ensures uopt: self_optimal(\old(*rd), msk) &&
		\old(rd->s.min) > -(int64_t)(msk >> 1) - 1
			==> eval_neg_unsigned_optimal(\old(*rd), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) &&
		\old(rd->s.min) > -(int64_t)(msk >> 1) - 1
			==> eval_neg_signed_optimal(\old(*rd), *rd, msk);
*/
void
eval_neg(struct bpf_reg_val *rd, size_t opsz, uint64_t msk)
{
	uint64_t ux, uy;
	int64_t sx, sy;
#ifdef FIX_NEG_SIGNED_32
	const int64_t smax_w = (int64_t)(msk >> 1);
	const int64_t smin_w = -smax_w - 1;
#endif
	struct bpf_reg_val cross_limits = {
		.s = { INT64_MIN, INT64_MAX },
		.u = { 0, UINT64_MAX },
	};

	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
		rd->u.min = (int32_t)rd->u.min;
		rd->u.max = (int32_t)rd->u.max;
	}

	if (rd->u.min == 0) {

		if (rd->u.max < (uint64_t)-INT64_MAX) {
			cross_limits.s.min = -rd->u.max;
			cross_limits.s.max = -rd->u.min;
		}

		if (rd->u.max != 0)
			rd->u.max = UINT64_MAX;

#ifdef FIX_NEG_ZERO

		if (rd->s.max <= 0)
			cross_limits.u.max = -(uint64_t)rd->s.min;
#endif
	} else {
		ux = -rd->u.min & msk;
		uy = -rd->u.max & msk;

		rd->u.max = RTE_MAX(ux, uy);
		rd->u.min = RTE_MIN(ux, uy);
	}

	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
		rd->s.min = (int32_t)rd->s.min;
		rd->s.max = (int32_t)rd->s.max;
	}

#ifdef FIX_NEG_SIGNED_32

	if (rd->s.min == smin_w) {

		if (rd->s.max <= 0) {
			cross_limits.u.min = -(uint64_t)rd->s.max & msk;
			cross_limits.u.max = -(uint64_t)rd->s.min & msk;
		}
		if (rd->s.max != smin_w)
			rd->s.max = smax_w;
	} else {

		sx = neg_sext(-rd->s.min & msk, msk);
		sy = neg_sext(-rd->s.max & msk, msk);

		rd->s.max = RTE_MAX(sx, sy);
		rd->s.min = RTE_MIN(sx, sy);
	}

	rd->s.min = neg_sext(RTE_MAX(rd->s.min, cross_limits.s.min) & msk, msk);
	rd->s.max = neg_sext(RTE_MIN(rd->s.max, cross_limits.s.max) & msk, msk);
#else
	if (rd->s.min == INT64_MIN) {
		if (rd->s.max <= 0) {
			cross_limits.u.min = -(uint64_t)rd->s.max;
			cross_limits.u.max = -(uint64_t)rd->s.min;
		}
		if (rd->s.max != INT64_MIN)
			rd->s.max = INT64_MAX;
	} else {
		sx = -rd->s.min & msk;
		sy = -rd->s.max & msk;

		rd->s.max = RTE_MAX(sx, sy);
		rd->s.min = RTE_MIN(sx, sy);
	}

	rd->s.min = RTE_MAX(rd->s.min, cross_limits.s.min) & msk;
	rd->s.max = RTE_MIN(rd->s.max, cross_limits.s.max) & msk;
#endif
	rd->u.min = RTE_MAX(rd->u.min, cross_limits.u.min) & msk;
	rd->u.max = RTE_MIN(rd->u.max, cross_limits.u.max) & msk;

#ifdef FIX_NEG_CROSS_INVERT

	if (rd->s.min > rd->s.max) {
		rd->s.max = (int64_t)(msk >> 1);
		rd->s.min = -rd->s.max - 1;
	}
	if (rd->u.min > rd->u.max) {
		rd->u.min = 0;
		rd->u.max = msk;
	}
#endif

	/*@ assert uopt_inv_umax:
	      neg_pat(neg_pat(rd->u.max, msk), msk) == rd->u.max; */
	/*@ assert uopt_inv_umin:
	      neg_pat(neg_pat(rd->u.min, msk), msk) == rd->u.min; */
	/*@ assert sopt_inv_smax:
	      neg_pat(neg_pat(((uint64_t)rd->s.max) & msk, msk), msk)
	        == (((uint64_t)rd->s.max) & msk); */
	/*@ assert sopt_inv_smin:
	      neg_pat(neg_pat(((uint64_t)rd->s.min) & msk, msk), msk)
	        == (((uint64_t)rd->s.min) & msk); */

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre), neg_pat(rd->u.max, msk), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre), neg_pat(rd->u.min, msk), msk); */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre),
	                   neg_pat(((uint64_t)rd->s.max) & msk, msk), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre),
	                   neg_pat(((uint64_t)rd->s.min) & msk, msk), msk); */
}
