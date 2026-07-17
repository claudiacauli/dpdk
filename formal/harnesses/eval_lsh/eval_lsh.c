#include "eval_lsh.h"
#include "../eval_max_bound/eval_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap. WP's typed memory model would otherwise
	// admit partial overlaps (rs == rd +/- a few words) that no C caller
	// can produce with two distinct struct objects; under such overlap the
	// stores to rd->u clobber the rs->u reads below and the ordering
	// ensures become falsifiable in-model. (The BMC harness likewise
	// forces prs = &rs; see eval_lsh_bmc.c.)
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
*/
void eval_lsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* check if shift value is less then max result bits */
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		/*@ assert full_slo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert full_shi: rd->s.max == (int64_t)(msk >> 1); */
		return;
	}

	/* check for overflow */
	if (rd->u.max > RTE_LEN2MASK(opsz - rs->u.max, uint64_t))
		eval_umax_bound(rd, msk);
	else {
		/*@ assert in_ord_d: rd->u.min <= rd->u.max; */
		/*@ assert in_ord_s: rs->u.min <= rs->u.max; */
		/*@ assert min_fits: rd->u.min <= RTE_LEN2MASK(opsz - rs->u.min, uint64_t); */
		rd->u.max <<= rs->u.max;
		rd->u.min <<= rs->u.min;
		/*@ assert umin_stone: rd->u.min <= msk; */
		/*@ assert uwidth_stone: rd->u.max <= msk; */
	}

	/* check that dreg values are and would remain always positive */
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
		/*@ assert smax_shift_id:
		      rd->s.max == \at(rd->s.max, Pre) << \at(rs->u.max, Pre); */
		/*@ assert smin_shift_id:
		      rd->s.min == \at(rd->s.min, Pre) << \at(rs->u.min, Pre); */
	}
}
