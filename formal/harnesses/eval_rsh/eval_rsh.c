#include "eval_rsh.h"
#include "../eval_max_bound/eval_max_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap. WP's typed memory model would otherwise
	// admit partial overlaps no C caller can produce, under which the
	// stores to rd->u clobber the rs->u reads below (see eval_lsh.c).
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
*/
void eval_rsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* check if shift value is less then max result bits */
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

	/* check that dreg values are always positive */
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
	}
}
