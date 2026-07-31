#include "eval_divmod.h"
#include "../eval_smax_bound/eval_smax_bound.h"

#include "axioms_div.h"

#ifdef FIX_DIVMOD_SIGNED_32

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t dm_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}
#endif

/*@
	requires op == BPF_DIV || op == BPF_MOD;
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	requires \separated(rd, rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures err_iff:   (\result != \null) <==>
		(\old(rd->u.min) == \old(rd->u.max) &&
		 \old(rs->u.min) == \old(rs->u.max) && \old(rs->u.max) == 0);
	ensures err_frame: \result != \null ==>
		rd->u == \old(rd->u) && rd->s == \old(rd->s);

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     \result == \null ==>
		eval_divmod_unsigned_soundness(op, \old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     \result == \null ==>
		eval_divmod_signed_soundness(op, \old(*rd), \old(*rs), *rd, msk);

	ensures uopt: \result == \null &&
		self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.min) == \old(rd->u.max) && \old(rs->u.min) == \old(rs->u.max)
			==> eval_divmod_unsigned_optimal(op, \old(*rd), \old(*rs), *rd, msk);
	ensures sopt: \result == \null &&
		self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.min) == \old(rd->u.max) && \old(rs->u.min) == \old(rs->u.max)
			==> eval_divmod_signed_optimal(op, \old(*rd), \old(*rs), *rd, msk);
*/
const char *
eval_divmod(uint32_t op, struct bpf_reg_val *rd, struct bpf_reg_val *rs,
	uint64_t msk)
{
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		if (rs->u.max == 0)
			return "division by 0";
		if (op == BPF_DIV) {
			rd->u.min /= rs->u.min;
			rd->u.max /= rs->u.max;
		} else {
			rd->u.min %= rs->u.min;
			rd->u.max %= rs->u.max;
		}
	} else {
		if (op == BPF_MOD)
			rd->u.max = RTE_MIN(rd->u.max, rs->u.max - 1);
		else
			rd->u.max = rd->u.max;
		rd->u.min = 0;
	}

#ifdef FIX_DIVMOD_SIGNED_32

	if (rd->u.min > (msk >> 1) || rd->u.max <= (msk >> 1)) {
		rd->s.min = dm_sext(rd->u.min, msk);
		rd->s.max = dm_sext(rd->u.max, msk);
	} else
#else
	if (rd->u.min >= (uint64_t)INT64_MIN || rd->u.max <= (uint64_t)INT64_MAX) {

		rd->s.min = rd->u.min;
		rd->s.max = rd->u.max;
	} else
#endif
		eval_smax_bound(rd, msk);

	return NULL;
}
