#include "eval_xor.h"
#include "../eval_uor_max/eval_uor_max.h"
#include "../eval_smax_bound/eval_smax_bound.h"

#include "axioms_xor.h"
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
	ensures usound:     eval_xor_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_xor_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	ensures uopt:
		un_witness(\old(*rd), rd->u.max, msk) &&
		un_witness(\old(*rd), rd->u.min, msk) &&
		un_witness(\old(*rs), 0, msk)
			==> eval_xor_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);

	ensures sopt:
		un_witness(\old(*rd), rd->s.max & msk, msk) &&
		un_witness(\old(*rd), rd->s.min & msk, msk) &&
		un_witness(\old(*rs), 0, msk)
			==> eval_xor_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_xor(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{

	/*@ assert mask_ite: msk == (opsz == 32 ? 0xFFFFFFFF : 0xFFFFFFFFFFFFFFFF); */
	/*@ assert uw_d: rd->u.max <= msk; */
	/*@ assert uw_s: rs->u.max <= msk; */
	/*@ assert sw_d: (uint64_t)rd->s.max <= (msk >> 1) || rd->s.max < 0; */
	/*@ assert sw_s: (uint64_t)rs->s.max <= (msk >> 1) || rs->s.max < 0; */

	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		/*@ assert uw_xor_c: (rd->u.max ^ rs->u.max) <= msk; */
		rd->u.min ^= rs->u.min;
		rd->u.max ^= rs->u.max;
	} else {
		rd->u.max = eval_uor_max(rd->u.max, rs->u.max, opsz);
		rd->u.min = 0;
	}

	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
		/*@ assert sw_xor_c:
		      -(msk >> 1) - 1 <= (rd->s.max ^ rs->s.max) &&
		      (rd->s.max ^ rs->s.max) <= (msk >> 1); */
		rd->s.min ^= rs->s.min;
		rd->s.max ^= rs->s.max;

	} else if (rd->s.min >= 0 && rs->s.min >= 0) {

		/*@ assert bn_half_d: (uint64_t)rd->s.max <= (msk >> 1); */
		/*@ assert bn_half_s: (uint64_t)rs->s.max <= (msk >> 1); */
		rd->s.max = eval_uor_max(rd->s.max, rs->s.max, opsz);
		rd->s.min = 0;
	} else
		eval_smax_bound(rd, msk);

	/*@ assert uopt_id_max: (rd->u.max ^ 0) == rd->u.max; */
	/*@ assert uopt_id_min: (rd->u.min ^ 0) == rd->u.min; */
	/*@ assert sopt_half_max: -(msk >> 1) - 1 <= rd->s.max <= (msk >> 1); */
	/*@ assert sopt_half_min: -(msk >> 1) - 1 <= rd->s.min <= (msk >> 1); */
	/*@ assert sopt_rt_max: to_signed(rd->s.max & msk, msk) == rd->s.max; */
	/*@ assert sopt_rt_min: to_signed(rd->s.min & msk, msk) == rd->s.min; */
	/*@ assert sopt_id_max: ((rd->s.max & msk) ^ 0) == (rd->s.max & msk); */
	/*@ assert sopt_id_min: ((rd->s.min & msk) ^ 0) == (rd->s.min & msk); */
}
