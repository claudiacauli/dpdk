#include "eval_sub.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	requires is_scalar_or_pointer(rs->v.type) && is_scalar_or_pointer(rd->v.type);
	requires range_validity(rd, msk) && range_validity(rs, msk);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar_or_pointer(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_sub_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_sub_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_sub(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)
{
	struct bpf_reg_val rv;

	rv.u.min = (rd->u.min - rs->u.max) & msk;
	rv.u.max = (rd->u.max - rs->u.min) & msk;
	rv.s.min = ((uint64_t)rd->s.min - (uint64_t)rs->s.max) & msk;
	rv.s.max = ((uint64_t)rd->s.max - (uint64_t)rs->s.min) & msk;

	#ifdef FIX_SUB_SIGNED_32
		/*
		* For 32-bit ops the masked differences above live in [0, 2^32)
		* (the signed value zero-extended), while rd/rs signed bounds and
		* the eval_smax_bound() reset use the sign-extended representation
		* ([INT32_MIN, INT32_MAX]). The overflow check below compares the
		* two representations directly, so a negative bound that wraps to
		* a large positive masked value can slip past it — and on the
		* both-constant path no check runs at all, so the wrapped value
		* flows straight into rd->s (BMC counterexample: (-1342177306) -
		* (-1342177292) = -14 tracked as 4294967282). Canonicalize to the
		* sign-extended form *before* the check so both sides speak the
		* same language.
		*/
		if (msk == _32_BIT_MASK) {
			/*
			* WP stepping stones, mirroring FIX_ADD_SIGNED_32 in
			* eval_add.c — see the rationale there. Differences of
			* canonical int32 bounds live in (-2^32, 2^32), so a
			* single +2^32 wrap-offset covers the masking and the
			* sign extension adds the usual three-case congruence.
			*/
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

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min > rd->u.min || rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);

	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.max < 0 && rv.s.min < rd->s.min) ||
			rv.s.min > rd->s.min) ||
			((rs->s.min < 0 && rv.s.max < rd->s.max) ||
			rv.s.max > rd->s.max)))
		eval_smax_bound(&rv, msk);

	rd->s = rv.s;
	rd->u = rv.u;
}
