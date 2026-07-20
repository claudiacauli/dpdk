#include "eval_sub.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
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
	ensures usound:     eval_sub_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_sub_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (sub-optimal). Mirrors add; anti-monotone in the subtrahend,
	// so the witness corners CROSS: u.max <- (rd.u.max, rs.u.min), u.min <-
	// (rd.u.min, rs.u.max). Soundness above is UNCONDITIONAL; op-optimality holds
	// from SELF-OPTIMAL operands in the NO-OVERFLOW regime (neither eval_umax_bound
	// nor eval_smax_bound fires). self_optimal supplies the corner un_witnesses
	// that form the bin_witness the existentials need.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.min) >= \old(rs->u.max)
			==> eval_sub_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		-(int64_t)(msk >> 1) - 1 <= \old(rd->s.min) - \old(rs->s.max) &&
		\old(rd->s.max) - \old(rs->s.min) <= (int64_t)(msk >> 1)
			==> eval_sub_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_sub(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)
{
	struct bpf_reg_val rv;

	rv.u.min = (rd->u.min - rs->u.max) & msk;
	rv.u.max = (rd->u.max - rs->u.min) & msk;
	/* uopt stone (add's uopt_nowrap, crossed): with rd.u.min >= rs.u.max both
	 * differences are non-negative, so `& msk` is the identity and the widening
	 * test below is false -- pinning the stored u endpoints to the corner diffs. */
	/*@ assert uopt_nowrap:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre)); */
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

	/* sopt stones (add's sopt_nowrap_*, crossed). After the 32-bit
	 * canonicalization so both widths speak sign-extended; the sext32_*_val
	 * disjunctions plus the guard exclude the +/-2^32 wrap cases. */
	/*@ assert sopt_nowrap_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre); */
	/*@ assert sopt_nowrap_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre); */

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min > rd->u.min || rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);

	/* uopt bridge: the corner diffs survive the unsigned widening test. */
	/*@ assert uopt_nowiden:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre)); */

#ifdef FIX_SUB_SIGNED_OVFL
	/*
	 * Precision (not soundness): same family as FIX_ADD_SIGNED_OVFL. The
	 * signed-overflow guards have UNGUARDED `rv.s.X > rd->s.X` terms. Subtracting
	 * a negative subtrahend bound legitimately INCREASES the result (rv.s.X >
	 * rd->s.X) with no overflow, yet that term fires and widens the whole signed
	 * track to [INT_MIN, INT_MAX] — so subtracting any negative-ranged value
	 * throws away signed precision. Guard the `>` terms by the subtrahend sign
	 * that actually admits underflow (min underflows only when rs->s.max >= 0;
	 * max underflows only when rs->s.min >= 0); the subtrahend-negative overflow
	 * wraps DOWN and is already the `rv.s.X < rd->s.X` term.
	 */
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.max < 0 && rv.s.min < rd->s.min) ||
			(rs->s.max >= 0 && rv.s.min > rd->s.min)) ||
			((rs->s.min < 0 && rv.s.max < rd->s.max) ||
			(rs->s.min >= 0 && rv.s.max > rd->s.max))))
		eval_smax_bound(&rv, msk);
#else
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.max < 0 && rv.s.min < rd->s.min) ||
			rv.s.min > rd->s.min) ||
			((rs->s.min < 0 && rv.s.max < rd->s.max) ||
			rv.s.max > rd->s.max)))
		eval_smax_bound(&rv, msk);
#endif

	/* Frame stones: the corner diffs reach the store intact (split per endpoint). */
	/*@ assert uopt_sum_rv_max:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre); */
	/*@ assert uopt_sum_rv_min:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre); */
	/*@ assert sopt_sum_rv_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre); */
	/*@ assert sopt_sum_rv_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) - \at(rs->s.max,Pre) &&
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre); */

	rd->s = rv.s;
	rd->u = rv.u;

	/* WITNESS + sum, ground instances. self_optimal gives un_witness at each
	 * operand's own endpoints; the CROSSED corner pairs are the bin_witnesses. */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        wrap_diff(\at(rd->u.max,Pre) - \at(rs->u.min,Pre), msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        wrap_diff(\at(rd->u.min,Pre) - \at(rs->u.max,Pre), msk) == rd->u.min; */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.min,Pre)) & msk, msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.max,Pre)) & msk, msk); */
}
