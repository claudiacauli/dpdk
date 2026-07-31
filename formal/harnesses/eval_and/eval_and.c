#include "eval_and.h"
#include "../eval_uand_max/eval_uand_max.h"
#include "../eval_smax_bound/eval_smax_bound.h"

#include "../../common/axioms_and.h"

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
	ensures usound:     eval_and_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_and_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

#ifdef PROVE_OPTIMALITY
	ensures uopt:
		un_witness(\old(*rd), rd->u.max, msk) &&
		un_witness(\old(*rs), rd->u.max, msk) &&
		un_witness(\old(*rd), rd->u.min, msk) &&
		un_witness(\old(*rs), rd->u.min, msk)
			==> eval_and_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);

	ensures sopt:
		un_witness(\old(*rd), rd->s.max & msk, msk) &&
		un_witness(\old(*rs), rd->s.max & msk, msk) &&
		un_witness(\old(*rd), rd->s.min & msk, msk) &&
		un_witness(\old(*rs), rd->s.min & msk, msk)
			==> eval_and_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
#endif
*/
void eval_and(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk)
{

	/*@ assert uw_d: rd->u.max <= msk; */
	/*@ assert uw_s: rs->u.max <= msk; */

	/*@ assert id_d: rd->s.min >= 0 ==>
	      ((uint64_t)rd->s.max & (msk >> 1)) == (uint64_t)rd->s.max; */
	/*@ assert id_s: rs->s.min >= 0 ==>
	      ((uint64_t)rs->s.max & (msk >> 1)) == (uint64_t)rs->s.max; */

	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		rd->u.min &= rs->u.min;
		rd->u.max &= rs->u.max;
	} else {
		rd->u.max = eval_uand_max(rd->u.max, rs->u.max, opsz);
		rd->u.min = 0;
	}

	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {

		rd->s.min &= rs->s.min;
		rd->s.max &= rs->s.max;
#ifdef FIX_AND_SIGNED_GUARD
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
		/*@ assert bn_half_d: (uint64_t)rd->s.max <= (msk >> 1); */
		/*@ assert bn_half_s: (uint64_t)rs->s.max <= (msk >> 1); */
		rd->s.max = eval_uand_max(rd->s.max & (msk >> 1),
			rs->s.max & (msk >> 1), opsz);
		rd->s.min = 0;

	} else if (rd->s.min >= 0 || rs->s.min >= 0) {
		int64_t nn = (rd->s.min >= 0) ? rd->s.max : rs->s.max;
		/*@ assert os_nn_nonneg: 0 <= nn; */
		/*@ assert os_nn_half: (uint64_t)nn <= (msk >> 1); */
		rd->s.max = eval_uand_max((uint64_t)nn & (msk >> 1),
			msk >> 1, opsz);
		rd->s.min = 0;
#else
	} else if (rd->s.min >= 0 || rs->s.min >= 0) {
		rd->s.max = eval_uand_max(rd->s.max & (msk >> 1),
			rs->s.max & (msk >> 1), opsz);
		rd->s.min = 0;
#endif
	} else
		eval_smax_bound(rd, msk);

#ifdef PROVE_OPTIMALITY

	/*@ assert uopt_idem_max: (rd->u.max & rd->u.max) == rd->u.max; */
	/*@ assert uopt_idem_min: (rd->u.min & rd->u.min) == rd->u.min; */

	/*@ assert sopt_half_max: -(msk >> 1) - 1 <= rd->s.max <= (msk >> 1); */
	/*@ assert sopt_half_min: -(msk >> 1) - 1 <= rd->s.min <= (msk >> 1); */
	/*@ assert sopt_rt_max: to_signed(rd->s.max & msk, msk) == rd->s.max; */
	/*@ assert sopt_rt_min: to_signed(rd->s.min & msk, msk) == rd->s.min; */
	/*@ assert sopt_idem_max:
	      ((rd->s.max & msk) & (rd->s.max & msk)) == (rd->s.max & msk); */
	/*@ assert sopt_idem_min:
	      ((rd->s.min & msk) & (rd->s.min & msk)) == (rd->s.min & msk); */
#endif
}
