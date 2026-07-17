#include "eval_arsh.h"
#include "../eval_max_bound/eval_max_bound.h"

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
	ensures usound:     eval_arsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_arsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_arsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	uint32_t shv;

	/* check if shift value is less then max result bits */
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		return;
	}

#ifdef FIX_ARSH_UNSIGNED_SIGN
	/*
	 * The u track holds PATTERNS, and ARSH interprets them as signed:
	 * the naive `(int64_t)u >> q` is wrong three ways (BMC
	 * counterexamples). (a) For 32-bit ops the sign sits at bit 31, not
	 * 63: pattern 0x85B28000 (negative int32) is a positive int64, so
	 * it shifts logically — [0, 0x92C40000] >> [17,20] yields
	 * [0, 18786] while the true result pattern is 0xFFFFC2D9. (b) For
	 * negative values a BIGGER shift moves the value up (toward -1), so
	 * the min/max amount pairing flips. (c) If the pattern interval
	 * spans the sign boundary the exact result is not an interval;
	 * widen to full width like the validator does elsewhere.
	 */
	{
		uint64_t half = msk >> 1;
		if (rd->u.min > half) {
			/* all negative: sign-extend, shift, re-encode */
			int64_t vmin = (opsz == 32) ?
				(int32_t)(uint32_t)rd->u.min : (int64_t)rd->u.min;
			int64_t vmax = (opsz == 32) ?
				(int32_t)(uint32_t)rd->u.max : (int64_t)rd->u.max;
			rd->u.min = ((uint64_t)(vmin >> rs->u.min)) & msk;
			rd->u.max = ((uint64_t)(vmax >> rs->u.max)) & msk;
		} else if (rd->u.max > half) {
			/* spans the sign boundary: no tight interval exists */
			rd->u.min = 0;
			rd->u.max = msk;
		} else {
			/* all non-negative: arithmetic == logical shift */
			rd->u.max >>= rs->u.min;
			rd->u.min >>= rs->u.max;
		}
	}
#else
	rd->u.max = (int64_t)rd->u.max >> rs->u.min;
	rd->u.min = (int64_t)rd->u.min >> rs->u.max;
#endif

	/* if we have 32-bit values - extend them to 64-bit */
	if (opsz == sizeof(uint32_t) * CHAR_BIT) {
	#ifdef FIX_ARSH_32EXT_SHL
		/*
		 * s.min/s.max are canonical int32 here and may be negative;
		 * left-shifting a negative signed value is formally UB
		 * (C11 6.5.7p4) even though every relevant compiler does
		 * the intended two's-complement shift. Shift in uint64
		 * (defined) and convert back — the same implementation-
		 * defined wrap FIX_ADD_SIGNED_32 already relies on.
		 */
		rd->s.min = (int64_t)((uint64_t)rd->s.min << opsz);
		rd->s.max = (int64_t)((uint64_t)rd->s.max << opsz);
	#else
		rd->s.min <<= opsz;
		rd->s.max <<= opsz;
	#endif
		shv = opsz;
	} else
		shv = 0;

	if (rd->s.min < 0)
		rd->s.min = (rd->s.min >> (rs->u.min + shv)) & msk;
	else
		rd->s.min = (rd->s.min >> (rs->u.max + shv)) & msk;

	if (rd->s.max < 0)
		rd->s.max = (rd->s.max >> (rs->u.max + shv)) & msk;
	else
		rd->s.max = (rd->s.max >> (rs->u.min + shv)) & msk;

#ifdef FIX_ARSH_SIGNED_MASK
	/*
	 * The `& msk` above zero-extends negative 32-bit results into huge
	 * positives (e.g. -2 becomes 4294967294), breaking s.min <= s.max
	 * and the canonical representation the rest of the validator
	 * assumes. BMC counterexample: msk32, s = [-993756161, 1610612736],
	 * shift [29,31] yields s = [4294967294, 3] while the true result 0
	 * escapes the interval. Sign-extend back to canonical form, the
	 * same sext32 idiom as FIX_ADD_SIGNED_32 / FIX_SUB_SIGNED_32.
	 * (64-bit ops: the mask is the identity and this is a no-op.)
	 */
	if (msk == _32_BIT_MASK) {
		rd->s.min = (int32_t)(uint32_t)rd->s.min;
		rd->s.max = (int32_t)(uint32_t)rd->s.max;
	}

	/*
	 * WP stepping stones: the whole 32ext dance (<<32, >>(q+32), & msk,
	 * sext32) nets out to a plain arithmetic shift of the entry value —
	 * these identities hand the ensures the bare `v >> q` terms the
	 * asr_* axioms reason about, instead of the four-layer composition.
	 * Only true with the mask fix applied, hence inside the gate.
	 */
	/*@ assert smax_shift_id:
	      rd->s.max == (\at(rd->s.max, Pre) < 0
	                    ? \at(rd->s.max, Pre) >> \at(rs->u.max, Pre)
	                    : \at(rd->s.max, Pre) >> \at(rs->u.min, Pre)); */
	/*@ assert smin_shift_id:
	      rd->s.min == (\at(rd->s.min, Pre) < 0
	                    ? \at(rd->s.min, Pre) >> \at(rs->u.min, Pre)
	                    : \at(rd->s.min, Pre) >> \at(rs->u.max, Pre)); */
#endif
}
