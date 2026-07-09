#include "eval_add.h"
#include "../eval_fill_max_bound/eval_fill_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"


/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	requires is_scalar_or_pointer(rs->v.type) && is_scalar_or_pointer(rd->v.type);
	requires range_validity(rd, msk) && range_validity(rs, msk);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns *rd;

	ensures type_ok:    is_scalar_or_pointer(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:	    eval_add_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_add_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_add(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)
{
	struct bpf_reg_val rs_buf;
	struct bpf_reg_val rv;

	if (RTE_BPF_ARG_PTR_TYPE(rs->v.type) != 0) {
		if (RTE_BPF_ARG_PTR_TYPE(rd->v.type) != 0) {
			/* treat sum of pointers as sum of two unknown scalars */
			eval_fill_max_bound(&rs_buf, msk);
			*rd = rs_buf;
			rs = &rs_buf;
		} else {
			/*
			 * rs is a pointer here and rd is not, so their v.type
			 * values differ => they are distinct objects. WP cannot
			 * derive separation from a value mismatch, so trust it
			 * (needed for the field read-backs below).
			 */
			//@ admit sep_else: \separated(rd, rs);
			/* scalar + pointer is a pointer of the same type */
			rd->v = rs->v;
		}
	}

	rv.u.min = (rd->u.min + rs->u.min) & msk;
	rv.u.max = (rd->u.max + rs->u.max) & msk;
	rv.s.min = ((uint64_t)rd->s.min + (uint64_t)rs->s.min) & msk;
	rv.s.max = ((uint64_t)rd->s.max + (uint64_t)rs->s.max) & msk;

	#ifdef FIX_ADD_SIGNED_32
		/*
		* For 32-bit ops the masked sums above live in [0, 2^32) (the
		* signed value zero-extended), while rd/rs signed bounds and the
		* eval_smax_bound() reset use the sign-extended representation
		* ([INT32_MIN, INT32_MAX]). The overflow check below compares the
		* two representations directly, so a negative bound that wraps to
		* a large positive masked value can slip past it and leave
		* s.min > s.max. Canonicalize to the sign-extended form *before*
		* the check so both sides speak the same language.
		*/
		if (msk == _32_BIT_MASK) {
			/*
			* WP stepping stones. Every rung below is load-bearing:
			* - *_rng before the sext: bound the masked value so the
			*   provers can strip the opaque to_sint64 store-wrapper
			*   (via land_le_mask); the land_* axiom triggers cannot
			*   fire through it otherwise.
			* - mask32_*: fold `& msk` into a piecewise-linear
			*   wrap-offset fact (land_id_u32 / land_wrap_u32_top).
			* - *_rng after the sext: canonical-int32 bounds; they
			*   pin the unique in-range case of sext32_*_val for ord
			*   and discharge the 32-bit half of swidth.
			* - sext32_*_val: the congruence interface ord consumes;
			*   downstream goals are pure linear arithmetic and never
			*   unfold `&` or the to_{u,s}int* conversions again.
			*/
			/*@ assert mask32_min_rng: 0 <= rv.s.min <= 0xFFFFFFFF; */
			/*@ assert mask32_max_rng: 0 <= rv.s.max <= 0xFFFFFFFF; */
			/*@ assert mask32_min:
			      rv.s.min == rd->s.min + rs->s.min ||
			      rv.s.min == rd->s.min + rs->s.min + 0x100000000; */
			/*@ assert mask32_max:
			      rv.s.max == rd->s.max + rs->s.max ||
			      rv.s.max == rd->s.max + rs->s.max + 0x100000000; */
			rv.s.min = (int32_t)(uint32_t)rv.s.min;
			rv.s.max = (int32_t)(uint32_t)rv.s.max;
			/*@ assert sext32_min_rng: INT32_MIN <= rv.s.min <= INT32_MAX; */
			/*@ assert sext32_max_rng: INT32_MIN <= rv.s.max <= INT32_MAX; */
			/*@ assert sext32_min_val:
			      rv.s.min == rd->s.min + rs->s.min ||
			      rv.s.min == rd->s.min + rs->s.min - 0x100000000 ||
			      rv.s.min == rd->s.min + rs->s.min + 0x100000000; */
			/*@ assert sext32_max_val:
			      rv.s.max == rd->s.max + rs->s.max ||
			      rv.s.max == rd->s.max + rs->s.max - 0x100000000 ||
			      rv.s.max == rd->s.max + rs->s.max + 0x100000000; */
		}
	#endif

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min < rd->u.min || rv.u.max < rd->u.max))
		eval_umax_bound(&rv, msk);

	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.min < 0 && rv.s.min > rd->s.min) ||
			rv.s.min < rd->s.min) ||
			((rs->s.max < 0 && rv.s.max > rd->s.max) ||
				rv.s.max < rd->s.max)))
		eval_smax_bound(&rv, msk);

	/*
	 * Split the ord goal: prove each half of range_ordering as its
	 * own (much smaller) obligation; the ensures then follows from
	 * store-forwarding alone.
	 */
	//@ assert ord_u: rv.u.min <= rv.u.max;
	//@ assert ord_s: rv.s.min <= rv.s.max;

	rd->s = rv.s;
	rd->u = rv.u;
}
