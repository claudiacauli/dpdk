#include "eval_add.h"
#include "../eval_fill_max_bound/eval_fill_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"


/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap — even for `add rX, rX`. WP's typed
	// memory model would otherwise admit partial overlaps no C caller
	// can produce; this replaces the former `admit sep_else` (same fact,
	// but proved against the caller contract instead of trusted mid-body).
	requires \separated(rd, rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns *rd;

	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:	    eval_add_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_add_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (add-optimal). Soundness above is UNCONDITIONAL; op-optimality
	// holds only from SELF-OPTIMAL operands in the NO-OVERFLOW regime (neither
	// eval_umax_bound nor eval_smax_bound fires) -- under overflow the range widens
	// to full width and op-optimality is lost. Witness for each endpoint is the
	// corresponding input-corner PAIR: self_optimal(rd) supplies un_witness at
	// rd.u.max/u.min and self_optimal(rs) at rs.u.max/u.min, which is exactly the
	// bin_witness the existential needs.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.max) + \old(rs->u.max) <= msk
			==> eval_add_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		-(int64_t)(msk >> 1) - 1 <= \old(rd->s.min) + \old(rs->s.min) &&
		\old(rd->s.max) + \old(rs->s.max) <= (int64_t)(msk >> 1)
			==> eval_add_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
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
			/* scalar + pointer is a pointer of the same type */
			rd->v = rs->v;
		}
	}

	rv.u.min = (rd->u.min + rs->u.min) & msk;
	rv.u.max = (rd->u.max + rs->u.max) & msk;
	/*
	 * uopt stepping stone. Under the no-overflow guard the corner sums do not
	 * wrap, so `& msk` is the identity here; that in turn makes the overflow
	 * test below false, pinning the stored u endpoints to the corner sums --
	 * exactly the witnesses eval_add_unsigned_optimal quantifies over. Asserted
	 * here, where only the guard and the preconditions are in scope.
	 */
	/*@ assert uopt_nowrap:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        (rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre)); */
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
	 * sopt stepping stones, the signed twins of uopt_nowrap. Placed AFTER the
	 * 32-bit canonicalization so both widths speak the sign-extended language:
	 * for msk32 the sext32_*_val disjunctions above plus the no-overflow guard
	 * exclude the +/-2^32 wrap cases; for msk64 the two's-complement sum is the
	 * mathematical sum outright. Split per endpoint to keep each goal small.
	 */
	/*@ assert sopt_nowrap_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre); */
	/*@ assert sopt_nowrap_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre); */

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min < rd->u.min || rv.u.max < rd->u.max))
		eval_umax_bound(&rv, msk);

	/* uopt bridge 1: under the guard the sums did not wrap, so rv.u.{max,min}
	 * are >= rd->u.{max,min} and the widening test above is FALSE -- the corner
	 * sums survive the branch. */
	/*@ assert uopt_nowiden:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        (rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre)); */

#ifdef FIX_ADD_SIGNED_OVFL
	/*
	 * Precision (not soundness): the upstream signed-overflow guards have an
	 * UNGUARDED `rv.s.X < rd->s.X` term. When the source bound rs->s.X is
	 * negative the sum legitimately DECREASES (rv.s.X < rd->s.X) with no
	 * overflow, yet that term fires and widens the whole signed track to
	 * [INT_MIN, INT_MAX] — so adding any negative-ranged value throws away all
	 * signed precision. Guard each `<` term with `rs->s.X >= 0` (its true
	 * overflow direction: the min/max wraps DOWN only when the addend is
	 * non-negative; the addend-negative underflow wraps UP and is already the
	 * `rv.s.X > rd->s.X` term). Sound: when rs->s.X < 0 and rv.s.X < rd->s.X
	 * there is no wrap.
	 */
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.min < 0 && rv.s.min > rd->s.min) ||
			(rs->s.min >= 0 && rv.s.min < rd->s.min)) ||
			((rs->s.max < 0 && rv.s.max > rd->s.max) ||
				(rs->s.max >= 0 && rv.s.max < rd->s.max))))
		eval_smax_bound(&rv, msk);
#else
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.min < 0 && rv.s.min > rd->s.min) ||
			rv.s.min < rd->s.min) ||
			((rs->s.max < 0 && rv.s.max > rd->s.max) ||
				rv.s.max < rd->s.max)))
		eval_smax_bound(&rv, msk);
#endif

	/*
	 * Split the ord goal: prove each half of range_ordering as its
	 * own (much smaller) obligation; the ensures then follows from
	 * store-forwarding alone.
	 */
	//@ assert ord_u: rv.u.min <= rv.u.max;
	//@ assert ord_s: rv.s.min <= rv.s.max;

	/* uopt FRAME step, split per endpoint. eval_smax_bound's assigns names only
	 * rv->s.{min,max}, so rv.u cannot have moved since uopt_nowiden -- but the
	 * conjunction (and the label-based \at form) both time out here, where the
	 * whole signed context is in scope. One endpoint at a time keeps each goal
	 * small enough to close. */
	/*@ assert uopt_sum_rv_max:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre); */
	/*@ assert uopt_sum_rv_min:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre); */

	/* sopt frame twins: under the no-signed-overflow guard the widening test
	 * above is FALSE, so eval_smax_bound did not fire and the corner sums
	 * established by sopt_nowrap_* survive to the store. */
	/*@ assert sopt_sum_rv_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre); */
	/*@ assert sopt_sum_rv_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre); */

	rd->s = rv.s;
	rd->u = rv.u;

	/*
	 * uopt WITNESS, as a GROUND instance: self-optimality of each operand makes
	 * its own u endpoints representable (un_witness), so the corner PAIR is a
	 * bin_witness; combined with uopt_nowrap above, the corner sums ARE the
	 * stored endpoints. Stating it on concrete terms means the provers discharge
	 * the postcondition's existentials by instantiation instead of search.
	 */
	/* Split four ways: each conjunct is its own (much smaller) obligation. The
	 * two _wit_ goals are pure unfolding of self_optimal -> un_witness; the two
	 * _sum_ goals are uopt_nowrap plus store-forwarding. */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        ((\at(rd->u.max,Pre) + \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        ((\at(rd->u.min,Pre) + \at(rs->u.min,Pre)) & msk) == rd->u.min; */

	/* sopt WITNESS + sum, the signed twins. self_optimal supplies un_witness at
	 * the signed endpoints' PATTERNS (pat(v) == (uint64_t)v & msk), so those form
	 * the bin_witness; the _sum_ goals then say the pattern-sum reads back as the
	 * stored signed endpoint -- which is sopt_sum_rv_* plus store-forwarding. */
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
	/*@ assert sopt_sum_smax:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
}
