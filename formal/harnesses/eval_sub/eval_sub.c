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

	// OP-OPTIMALITY (sub-optimal). Mirrors add; anti-monotone in the subtrahend, so
	// the witness corners CROSS: u.max <- (rd.u.max, rs.u.min), u.min <- (rd.u.min,
	// rs.u.max). Soundness above is UNCONDITIONAL. self_optimal supplies the corner
	// un_witnesses that form the bin_witness the existentials need.
	//
	// With the borrow-parity underflow tests in the body (FIX_SUB_UNSIGNED_OVFL /
	// FIX_SUB_SIGNED_OVFL_OPT) the guard weakens from NO-underflow to UNIFORM
	// underflow -- both crossed corners in the same wrap regime (equal borrow bits /
	// equal trits). Under it the kept output endpoints ARE the wrapped corner
	// diffs, attained by the crossed corner pairs self_optimal supplies. NOT
	// unconditional: under a wrap MISMATCH the body widens to top, whose endpoints
	// are interior points the intersection gamma need not contain (brute-refuted at
	// W=3/4, see eval_add's note; the guarded forms are brute-CLEAN with ~1.5x the
	// unsigned coverage of the old guard -- scratchpad brute_guarded.c). Without a
	// track's fix, that track keeps the old NO-underflow guard.
	// SINGLE CONTRACT OF RECORD (fixed semantics): under --no-fixes these two
	// clauses go red on the both-wrap regime -- documenting the upstream
	// imprecision the FIX_SUB_* body fixes repair.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->u.min) < \old(rs->u.max)) <==>
		 (\old(rd->u.max) < \old(rs->u.min)))
			==> eval_sub_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->s.min) - \old(rs->s.max) < -(int64_t)(msk >> 1) - 1) <==>
		 (\old(rd->s.max) - \old(rs->s.min) < -(int64_t)(msk >> 1) - 1)) &&
		((\old(rd->s.min) - \old(rs->s.max) > (int64_t)(msk >> 1)) <==>
		 (\old(rd->s.max) - \old(rs->s.min) > (int64_t)(msk >> 1)))
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
#ifdef FIX_SUB_UNSIGNED_OVFL
	/* BOTH-BORROW twin: max-corner borrow implies min-corner borrow (the min
	 * diff is the smaller), both masked diffs rise by exactly msk+1, the borrow
	 * bits agree, the parity test below is FALSE, and the wrapped corner diffs
	 * survive. Linear form on purpose. */
	/*@ assert uopt_nowrap_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1 &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1); */
#endif
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
#ifdef FIX_SUB_SIGNED_OVFL_OPT
	/* Sign helpers for the crossed corners (see eval_add's sopt_*_signs note:
	 * without these the _min wrap stones spin their full ceiling). Both-
	 * OVERFLOW of the min diff forces a non-negative minuend track and a
	 * negative subtrahend track; both-UNDERFLOW of the max diff mirrors.
	 * Linear from the width requires. */
	/*@ assert sopt_of_signs:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        0 <= \at(rd->s.min,Pre) && \at(rs->s.max,Pre) < 0; */
	/*@ assert sopt_uf_signs:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        \at(rd->s.max,Pre) < 0 && 0 < \at(rs->s.min,Pre); */
	/* 64-bit value pins (see eval_add's sext64_*_val note; crossed corners). */
	/*@ assert sext64_min_val: msk == _64_BIT_MASK ==>
	      (rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) ||
	       rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - 0x10000000000000000 ||
	       rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + 0x10000000000000000); */
	/*@ assert sext64_max_val: msk == _64_BIT_MASK ==>
	      (rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) ||
	       rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - 0x10000000000000000 ||
	       rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + 0x10000000000000000); */
	/* Uniform-wrap twins (crossed corners: min diff = smin_d - smax_s, max diff
	 * = smax_d - smin_s). Both-OVERFLOW: the min diff already exceeds SMAX_w;
	 * every masked diff re-reads as diff - (msk+1). Both-UNDERFLOW: the max
	 * diff is below SMIN_w; every masked diff re-reads as diff + (msk+1). */
	/*@ assert sopt_ofwrap_min:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_ofwrap_max:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_ufwrap_min:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + msk + 1; */
	/*@ assert sopt_ufwrap_max:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + msk + 1; */
#endif

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
#ifdef FIX_SUB_UNSIGNED_OVFL
	/*
	 * Optimal unsigned underflow handling, the subtraction twin of eval_add's
	 * carry-parity test. `rv.u.X > rd->u.X` is the BORROW bit of corner X (the
	 * masked difference rose above the minuend iff it went negative and wrapped up
	 * by 2^w). The masked corner-diff interval is the EXACT reachable set exactly
	 * when both corners borrow the SAME amount; a MISMATCH is the only case the band
	 * straddles the 0 / 2^w seam, where no interval beats [0,msk] (itself optimal:
	 * the crossed boundary attains both endpoints). Widen on borrow MISMATCH (!=),
	 * not on any borrow (the old ||). Subsumes the former constant special-case.
	 */
	if ((rv.u.min > rd->u.min) != (rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);
#else
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min > rd->u.min || rv.u.max > rd->u.max))
		eval_umax_bound(&rv, msk);
#endif

	/* uopt bridge: the corner diffs survive the unsigned widening test. */
	/*@ assert uopt_nowiden:
	      \at(rd->u.min,Pre) >= \at(rs->u.max,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre)); */
#ifdef FIX_SUB_UNSIGNED_OVFL
	/*@ assert uopt_nowiden_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        (rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1 &&
	         rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1); */
#endif

#if defined(FIX_SUB_SIGNED_OVFL_OPT)
	/*
	 * Optimal signed underflow handling: the two's-complement twin of the unsigned
	 * borrow-parity test above, and the exact mirror of eval_add's signed fix. Each
	 * corner's wrap DIRECTION is a trit: underflow-up (subtrahend >= 0 yet the
	 * result ROSE) and overflow-down (subtrahend < 0 yet the result FELL). Because
	 * the crossed corner diffs are ordered (rd.s.min-rs.s.max <= rd.s.max-rs.s.min)
	 * the min corner's trit is <= the max corner's, so equal trits are exactly the
	 * uniform wraps whose masked corner interval is the EXACT signed image; a
	 * mismatch is the only straddle of the signed seam, where [INT_MIN,INT_MAX] is
	 * op-optimal. Widen on direction MISMATCH. Supersedes the two branches below (it
	 * fixes the negative-subtrahend over-widening AND the uniform-wrap one); subsumes
	 * the constant special-case.
	 */
	{
		int uf_min = (rs->s.max >= 0 && rv.s.min > rd->s.min);
		int of_min = (rs->s.max < 0 && rv.s.min < rd->s.min);
		int uf_max = (rs->s.min >= 0 && rv.s.max > rd->s.max);
		int of_max = (rs->s.min < 0 && rv.s.max < rd->s.max);
		if (uf_min != uf_max || of_min != of_max)
			eval_smax_bound(&rv, msk);
	}
#elif defined(FIX_SUB_SIGNED_OVFL)
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
#ifdef FIX_SUB_UNSIGNED_OVFL
	/* Both-borrow frame twins. */
	/*@ assert uopt_sum_rv_max_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        rv.u.max == \at(rd->u.max,Pre) - \at(rs->u.min,Pre) + msk + 1; */
	/*@ assert uopt_sum_rv_min_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        rv.u.min == \at(rd->u.min,Pre) - \at(rs->u.max,Pre) + msk + 1; */
#endif
#ifdef FIX_SUB_SIGNED_OVFL_OPT
	/* Uniform-wrap frame twins: under equal trits the parity test was FALSE and
	 * the wrapped corner diffs reach the store. */
	/*@ assert sopt_sum_rv_min_of:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_max_of:
	      \at(rd->s.min,Pre) - \at(rs->s.max,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_min_uf:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) - \at(rs->s.max,Pre) + msk + 1; */
	/*@ assert sopt_sum_rv_max_uf:
	      \at(rd->s.max,Pre) - \at(rs->s.min,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) - \at(rs->s.min,Pre) + msk + 1; */
#endif

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
#ifdef FIX_SUB_UNSIGNED_OVFL
	/* Both-borrow ground twins: wrap_diff unfolds to the +msk+1 branch, matching
	 * uopt_sum_rv_*_w plus store-forwarding. */
	/*@ assert uopt_sum_umax_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        wrap_diff(\at(rd->u.max,Pre) - \at(rs->u.min,Pre), msk) == rd->u.max; */
	/*@ assert uopt_sum_umin_w:
	      \at(rd->u.max,Pre) < \at(rs->u.min,Pre) ==>
	        wrap_diff(\at(rd->u.min,Pre) - \at(rs->u.max,Pre), msk) == rd->u.min; */
#endif
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
