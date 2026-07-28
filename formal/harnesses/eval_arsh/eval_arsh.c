#include "eval_arsh.h"
#include "lemmas_canon_arsh.h"
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

	// OP-OPTIMALITY (arsh-optimal). Sign-aware: for negatives a bigger shift
	// moves the value UP, so monotonicity in the shift flips by sign (the code
	// picks the shift corner per sign, which is why the witnesses below carry
	// the same conditional). Soundness is UNCONDITIONAL; op-optimality needs
	// shift < width. Unlike eval_lsh/eval_rsh the SIGNED track has no widening
	// branch at all past the early return, so its endpoints are always the
	// per-sign corners -- the shift is total on the canonical value.
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk)
			==> eval_arsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
	// The UNSIGNED track carries patterns, and arsh reads them as signed, so
	// it additionally needs the pattern interval NOT to span the sign
	// boundary: a spanning interval has no tight image (the result wraps from
	// large-positive to small-negative patterns) and the code correctly
	// widens to [0, msk]. Off the spanning case the corners are the per-sign
	// ones, CROSSED for an all-negative interval and UNCROSSED for an
	// all-non-negative one -- the conditional the witnesses below carry.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) &&
		(\old(rd->u.min) > (msk >> 1) || \old(rd->u.max) <= (msk >> 1))
			==> eval_arsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	// Both optimality clauses are FIX-GATED IN EFFECT: proved under --fixes,
	// and EXPECTED to fail under --no-fixes, where they join this operator's
	// bug report alongside usound/ssound. That is the correct signal -- the
	// unfixed code is genuinely not op-optimal (see the FIX_ARSH_UNSIGNED_SIGN
	// counterexamples below). The ensures themselves stay ungated and
	// uncommented, like every other clause in this contract.
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
			/* The per-width sign-extension the code open-codes IS
			 * to_signed at that width -- state it once here so the
			 * _sum_ stones below can speak in to_signed terms. */
			/*@ check uopt_sext_min:
			      vmin == to_signed(\at(rd->u.min,Pre), msk); */
			/*@ check uopt_sext_max:
			      vmax == to_signed(\at(rd->u.max,Pre), msk); */
			rd->u.min = ((uint64_t)(vmin >> rs->u.min)) & msk;
			rd->u.max = ((uint64_t)(vmax >> rs->u.max)) & msk;
			/* All-negative corners: a BIGGER shift moves a negative
			 * value UP, so max takes the max shift (CROSSED relative
			 * to the non-negative branch below). */
			/*@ check uopt_sum_neg_umax:
			      (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk) == rd->u.max; */
			/*@ check uopt_sum_neg_umin:
			      (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk) == rd->u.min; */
			/* assert twins of the two checks above, in the EXACT
			 * bracket-hypothesis shape of arsh_usound_neg32
			 * (lemmas_canon_arsh.h), so its instantiation at the
			 * usound part-04 PO discharges reflexively. Asserts,
			 * not checks, ON PURPOSE: the lemma needs them as
			 * downstream hypotheses (2026-07-28). */
			/*@ assert usound_link_neg_umax:
			      rd->u.max == (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk); */
			/*@ assert usound_link_neg_umin:
			      rd->u.min == (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk); */
		} else if (rd->u.max > half) {
			/* spans the sign boundary: no tight interval exists */
			rd->u.min = 0;
			rd->u.max = msk;
		} else {
			/* all non-negative: arithmetic == logical shift */
			rd->u.max >>= rs->u.min;
			rd->u.min >>= rs->u.max;
			/* All-non-negative corners: to_signed is the identity
			 * here and the re-encoding mask is a no-op, so these
			 * reduce to the plain logical shifts just performed --
			 * UNCROSSED, max takes the min shift. */
			/*@ check uopt_sum_pos_umax:
			      (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
			         >> \at(rs->u.min,Pre))) & msk) == rd->u.max; */
			/*@ check uopt_sum_pos_umin:
			      (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
			         >> \at(rs->u.max,Pre))) & msk) == rd->u.min; */
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

	/*
	 * OP-OPTIMALITY witnesses (ground instances) for the signed track.
	 * self_optimal(rd) supplies un_witness at the PATTERN of each signed
	 * endpoint, self_optimal(rs) supplies it at each shift endpoint, so the
	 * per-sign corner pairs are bin_witnesses. The shift component carries
	 * the same sign conditional the code uses: for a negative endpoint a
	 * LARGER shift moves the value up toward -1, so s.max pairs with u.max
	 * when negative and u.min when not (and s.min mirrors it).
	 *
	 * The _sum_ stones then say those corners shift to the stored endpoints.
	 * They cross from the pattern representation the witness uses to the
	 * canonical one shift_id speaks of, which is exactly to_signed_canon_rt
	 * (common/axioms_shift_opt.h) -- a WP-proved lemma, not a trusted axiom.
	 * No branch-selection stone is needed here: nothing in the signed track
	 * widens, so there is no widening branch to exclude.
	 *
	 * WHY `check` AND NOT `assert` (applies to every uopt_/sopt_ stone in
	 * this function). An `assert` is ASSUMED by every later PO, and these sit
	 * at function end -- i.e. before the `ensures` program point -- so as
	 * asserts they became hypotheses in every usound/ssound PO too. That was
	 * not free: it cost eval_arsh's usound three extra timing-out split parts
	 * (96/97 in 30m -> 93/97 in 60m) and doubled the wall clock.
	 *
	 * A `check` is VERIFIED but NOT ASSUMED, so it pollutes nothing. Unlike
	 * eval_lsh/eval_rsh -- whose chains genuinely need their branch-selection
	 * facts carried forward as hypotheses -- these stones turned out to be
	 * prophylactic: they were written by following the eval_add recipe, but
	 * uopt and sopt each prove 97/97 WITHOUT them being assumed. So they are
	 * kept as machine-checked documentation of the witness structure at zero
	 * cost to the soundness proofs. If a future edit makes an optimality goal
	 * depend on one of them, that goal will fail loudly rather than silently
	 * leaning on an assumption -- which is the safer failure mode anyway.
	 */
	/*@ check sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    (\at(rd->s.max,Pre) < 0 ? \at(rs->u.max,Pre)
	                                            : \at(rs->u.min,Pre)), msk); */
	/*@ check sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    (\at(rd->s.min,Pre) < 0 ? \at(rs->u.min,Pre)
	                                            : \at(rs->u.max,Pre)), msk); */
	/*@ check sopt_sum_smax:
	      (to_signed(((uint64_t)\at(rd->s.max,Pre)) & msk, msk)
	       >> (\at(rd->s.max,Pre) < 0 ? \at(rs->u.max,Pre)
	                                  : \at(rs->u.min,Pre))) == rd->s.max; */
	/*@ check sopt_sum_smin:
	      (to_signed(((uint64_t)\at(rd->s.min,Pre)) & msk, msk)
	       >> (\at(rd->s.min,Pre) < 0 ? \at(rs->u.min,Pre)
	                                  : \at(rs->u.max,Pre))) == rd->s.min; */
#endif

	/*
	 * OP-OPTIMALITY witnesses and post-merge restatements for the UNSIGNED
	 * track. Here the witness is the pattern endpoint itself (self_optimal's
	 * u.min/u.max conjuncts), and the shift component carries the sign
	 * conditional: the all-negative branch pairs u.max with the LARGER shift,
	 * the all-non-negative branch with the smaller one.
	 *
	 * The uopt guard rules out the middle (sign-spanning) branch by plain
	 * arithmetic -- `u.min > half || u.max <= half` is exactly the negation
	 * of `!(u.min > half) && (u.max > half)' -- so unlike eval_lsh no shift
	 * identity is needed to select the branch. The restatements below still
	 * have to re-derive the two surviving branches' facts past the merge.
	 */
	/*@ check uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre), \at(rd->u.max,Pre),
	                    (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.max,Pre)
	                                                     : \at(rs->u.min,Pre)),
	                    msk); */
	/*@ check uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre), \at(rd->u.min,Pre),
	                    (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.min,Pre)
	                                                     : \at(rs->u.max,Pre)),
	                    msk); */
	/*@ check uopt_sum_end_umax:
	      (\at(rd->u.min,Pre) > (msk >> 1) ||
	       \at(rd->u.max,Pre) <= (msk >> 1)) ==>
	        (((uint64_t)(to_signed(\at(rd->u.max,Pre), msk)
	           >> (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.max,Pre)
	                                               : \at(rs->u.min,Pre))))
	         & msk) == rd->u.max; */
	/*@ check uopt_sum_end_umin:
	      (\at(rd->u.min,Pre) > (msk >> 1) ||
	       \at(rd->u.max,Pre) <= (msk >> 1)) ==>
	        (((uint64_t)(to_signed(\at(rd->u.min,Pre), msk)
	           >> (\at(rd->u.min,Pre) > (msk >> 1) ? \at(rs->u.min,Pre)
	                                               : \at(rs->u.max,Pre))))
	         & msk) == rd->u.min; */
}
