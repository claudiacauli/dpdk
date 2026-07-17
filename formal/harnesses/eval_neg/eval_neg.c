#include "eval_neg.h"

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
	requires range_validity(rd, msk);
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
}
