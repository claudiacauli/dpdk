#include "eval_neg.h"
/*
 * NOTE (2026-07-20): do NOT add common/lemmas_canon.h here. It was
 * tried as the ssound fix (the PO derives every signed output endpoint
 * as to_signed(((uint64_t)w) & msk, msk), which is exactly
 * to_signed_canon_rt's shape) and it REGRESSED usound — green in 10s
 * without the include, 0/1 at 300s with it — while ssound stayed red.
 * A TU-wide lemma is too blunt for this TU; the round-trip fact has to
 * arrive as a narrow in-body stone with the exact goal term shape.
 * ssound remains the one open eval_neg goal.
 */

#ifdef FIX_NEG_SIGNED_32
/*
 * Sign-extend the low-w-bit pattern p (in [0, msk]) to its canonical
 * signed value — the C computation of to_signed(p, msk). Same helper as
 * eval_mul's mul_sext / eval_divmod's dm_sext.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t neg_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}
#endif

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd);
	requires is_scalar(rd->v.type);
	// Relaxed from range_validity to range_ordering (2026-07-19), enabled by
	// FIX_NEG_CROSS_INVERT below. The intersection-soundness refactor dropped
	// range_validity from every other operator; eval_neg was missed, and the
	// only thing still needing agreement was uord/sord -- the cross-track
	// clamps could cross and emit an EMPTY interval. Guarding that directly is
	// strictly better than demanding agreement from the caller, because
	// eval_apply_mask cannot supply it: BMC grid (eval_neg_pre_bmc.c) shows
	// apply_mask ESTABLISHES ordering but never agreement, while eval_neg with
	// the guard is SUFFICIENT from ordering alone. That in turn retires
	// eval_alu's `vld_d` stone, which was false at its call site.
	requires range_ordering(rd);
	requires range_within_width(rd, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_neg_unsigned_soundness(\old(*rd), *rd, msk);
	ensures ssound:     eval_neg_signed_soundness(\old(*rd), *rd, msk);

	// OP-OPTIMALITY (neg-optimal). Soundness above stays UNCONDITIONAL;
	// op-optimality is conditional on a SELF-OPTIMAL input plus exclusion of the
	// width-min (INT_MIN) wrap, which negates to itself and breaks
	// anti-monotonicity -- BMC (eval_neg_opt_bmc.c, both widths) showed that is
	// the lone residual, and the same two guards appear there as the
	// self_optimal REQUIREs plus BMC_NOWRAP.
	//
	// The witness is forced, which is what makes this provable: neg_pat is an
	// INVOLUTION on [0, msk], so the only value that can attain an output
	// endpoint e is neg_pat(e) -- there is nothing to search for. self_optimal
	// then discharges that the preimage is representable.
	ensures uopt: self_optimal(\old(*rd), msk) &&
		\old(rd->s.min) > -(int64_t)(msk >> 1) - 1
			==> eval_neg_unsigned_optimal(\old(*rd), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) &&
		\old(rd->s.min) > -(int64_t)(msk >> 1) - 1
			==> eval_neg_signed_optimal(\old(*rd), *rd, msk);
*/
void
eval_neg(struct bpf_reg_val *rd, size_t opsz, uint64_t msk)
{
	uint64_t ux, uy;
	int64_t sx, sy;
#ifdef FIX_NEG_SIGNED_32
	/* the mask's own signed boundaries: INT32_MIN/MAX or INT64_MIN/MAX */
	const int64_t smax_w = (int64_t)(msk >> 1);
	const int64_t smin_w = -smax_w - 1;
#endif
	/* additional limits imposed by signed on unsigned and back */
	struct bpf_reg_val cross_limits = {
		.s = { INT64_MIN, INT64_MAX },
		.u = { 0, UINT64_MAX },
	};

	/* if we have 32-bit values - extend them to 64-bit */
	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
		rd->u.min = (int32_t)rd->u.min;
		rd->u.max = (int32_t)rd->u.max;
	}

	if (rd->u.min == 0) {
		/* special case: ranges that include 0 and, possibly, 1 */

		/*
		 * Calculate requirements on the signed range of negation.
		 * It is only possible when negated range does not cross from
		 * INT64_MIN to INT64_MAX, which means our original range does
		 * not reach (uint64_t)-INT64_MAX.
		 */
		if (rd->u.max < (uint64_t)-INT64_MAX) {
			cross_limits.s.min = -rd->u.max;
			cross_limits.s.max = -rd->u.min;
		}

		if (rd->u.max != 0)
			rd->u.max = UINT64_MAX;

#ifdef FIX_NEG_ZERO
		/*
		 * Precision (not soundness): the widening above sets u.max to the
		 * full width, but under the intersection semantics with a SELF-OPTIMAL
		 * input, if s.max <= 0 there is no representable positive, so no
		 * pattern negates into the high half and the unsigned image tops
		 * out at -s.min. (Self-optimality guarantees pattern(s.min) <= u.max, so
		 * s.min is representable and -s.min IS attained — the self-suboptimal
		 * truncation case where this would overshoot is excluded by the
		 * op-optimality precondition.) Bound u.max via cross_limits; generalizes
		 * the s.min == INT_MIN wrap case below.
		 */
		if (rd->s.max <= 0)
			cross_limits.u.max = -(uint64_t)rd->s.min;
#endif
	} else {
		ux = -rd->u.min & msk;
		uy = -rd->u.max & msk;

		rd->u.max = RTE_MAX(ux, uy);
		rd->u.min = RTE_MIN(ux, uy);
	}

	/* if we have 32-bit values - extend them to 64-bit */
	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
		rd->s.min = (int32_t)rd->s.min;
		rd->s.max = (int32_t)rd->s.max;
	}

#ifdef FIX_NEG_SIGNED_32
	/*
	 * Upstream's signed track is broken for 32-bit ops in two ways.
	 * (1) It stores w-bit PATTERNS: `-s & msk` zero-extends, so NEG of
	 *     the constant 5 is tracked as s = [0xFFFFFFFB, 0xFFFFFFFB]
	 *     instead of [-5, -5] — swidth and ssound break (the canonical
	 *     reading is negative), and the final `& msk` clamp re-breaks
	 *     canonicity even for ranges that survive. Same family as
	 *     FIX_MUL_SCONST / FIX_DIVMOD_SIGNED_32.
	 * (2) The wrap special-case guards on INT64_MIN only, but the value
	 *     whose negation wraps in w bits is the MASK's own minimum
	 *     -(msk>>1)-1: for a 32-bit range [-2^31, -2^31+5] the else
	 *     branch's endpoint interval misses negated values up to
	 *     2^31-1 — unsound even with (1) repaired.
	 * Fix: guard on the mask-relative minimum, build the cross-limit
	 * patterns with an explicit `& msk`, negate canonically (mask, then
	 * sign-extend), and sign-extend after the final clamp. For
	 * msk == 2^64-1 every changed expression is value-identical to the
	 * original.
	 *
	 * Violates (unfixed): swidth, ssound — WP no-fixes run (exactly
	 * those two ensures fail, 0/1 each; uord/sord/uwidth/usound all
	 * still prove) and ESBMC BMC_32 witness (range_within_width). The
	 * 64-bit path is clean: orig-64 BMC passes on the full domain.
	 */
	if (rd->s.min == smin_w) {
		/* special case: negation of the width's INT_MIN wraps to
		 * itself */
		if (rd->s.max <= 0) {
			cross_limits.u.min = -(uint64_t)rd->s.max & msk;
			cross_limits.u.max = -(uint64_t)rd->s.min & msk;
		}
		if (rd->s.max != smin_w)
			rd->s.max = smax_w;
	} else {
		/* since max >= min, neither can be smin_w here: negation is
		 * anti-monotone and wrap-free, and the masked pattern
		 * sign-extends back to the exact canonical value */
		sx = neg_sext(-rd->s.min & msk, msk);
		sy = neg_sext(-rd->s.max & msk, msk);

		rd->s.max = RTE_MAX(sx, sy);
		rd->s.min = RTE_MIN(sx, sy);
	}

	rd->s.min = neg_sext(RTE_MAX(rd->s.min, cross_limits.s.min) & msk, msk);
	rd->s.max = neg_sext(RTE_MIN(rd->s.max, cross_limits.s.max) & msk, msk);
#else
	if (rd->s.min == INT64_MIN) {
		/* special case: negation of INT64_MIN is INT64_MIN */
		if (rd->s.max <= 0) {
			cross_limits.u.min = -(uint64_t)rd->s.max;
			cross_limits.u.max = -(uint64_t)rd->s.min;
		}
		if (rd->s.max != INT64_MIN)
			rd->s.max = INT64_MAX;
	} else {
		/* since max >= min, neither can be INT64_MIN here */
		sx = -rd->s.min & msk;
		sy = -rd->s.max & msk;

		rd->s.max = RTE_MAX(sx, sy);
		rd->s.min = RTE_MIN(sx, sy);
	}

	rd->s.min = RTE_MAX(rd->s.min, cross_limits.s.min) & msk;
	rd->s.max = RTE_MIN(rd->s.max, cross_limits.s.max) & msk;
#endif
	rd->u.min = RTE_MAX(rd->u.min, cross_limits.u.min) & msk;
	rd->u.max = RTE_MIN(rd->u.max, cross_limits.u.max) & msk;

#ifdef FIX_NEG_CROSS_INVERT
	/*
	 * The four clamps above pull from OPPOSITE directions: each min is
	 * raised toward a cross-track limit while the matching max is lowered
	 * toward another. When the two tracks disagree the limits pass each
	 * other and the interval INVERTS -- e.g. u=[0,10], s=[-3,-1] at msk64
	 * gives cross_s=[-10,0] against a negated s of [1,3], so
	 * s.min = MAX(1,-10) = 1 and s.max = MIN(3,0) = 0, i.e. s=[1,0].
	 *
	 * An inverted interval denotes the EMPTY set, so every downstream range
	 * check on the register is vacuously satisfiable -- the unsound
	 * direction. Upstream never detects this: no operator re-checks
	 * ordering after a cross-track clamp.
	 *
	 * Repair (same shape as FIX_APPLY_MASK_SIGNED): if a clamp pair
	 * crossed, the cross-track information was contradictory, so keep no
	 * information rather than empty information -- widen that track to the
	 * width's full range. Sound and non-empty; imprecise only on inputs
	 * that were already inconsistent.
	 */
	if (rd->s.min > rd->s.max) {
		rd->s.max = (int64_t)(msk >> 1);
		rd->s.min = -rd->s.max - 1;
	}
	if (rd->u.min > rd->u.max) {
		rd->u.min = 0;
		rd->u.max = msk;
	}
#endif

	/*
	 * OP-OPTIMALITY stones. neg_pat is an involution on [0,msk], so the
	 * witness for output endpoint e is forced to be neg_pat(e) -- the
	 * existential has exactly one candidate and nothing is searched for. Each
	 * _wit_ stone says that forced preimage is representable in the INPUT
	 * (which is what self_optimal buys); each _inv_ stone is the involution
	 * instance that turns it back into the endpoint.
	 */
	/*@ assert uopt_inv_umax:
	      neg_pat(neg_pat(rd->u.max, msk), msk) == rd->u.max; */
	/*@ assert uopt_inv_umin:
	      neg_pat(neg_pat(rd->u.min, msk), msk) == rd->u.min; */
	/*@ assert sopt_inv_smax:
	      neg_pat(neg_pat(((uint64_t)rd->s.max) & msk, msk), msk)
	        == (((uint64_t)rd->s.max) & msk); */
	/*@ assert sopt_inv_smin:
	      neg_pat(neg_pat(((uint64_t)rd->s.min) & msk, msk), msk)
	        == (((uint64_t)rd->s.min) & msk); */

	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre), neg_pat(rd->u.max, msk), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre), neg_pat(rd->u.min, msk), msk); */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre),
	                   neg_pat(((uint64_t)rd->s.max) & msk, msk), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) &&
	      \at(rd->s.min,Pre) > -(int64_t)(msk >> 1) - 1 ==>
	        un_witness(\at(*rd,Pre),
	                   neg_pat(((uint64_t)rd->s.min) & msk, msk), msk); */
}
