#include "eval_apply_mask.h"
/* to_signed_canon_rt: the sopt witness is the canonical endpoint itself, and
 * the predicate re-encodes it as a pattern before decoding, so the chain has
 * to cross representations exactly once. See common/lemmas_canon.h. */
#include "../../common/lemmas_canon.h"
/* Block algebra for FIX_APPLY_MASK_OPT (uord/usound/uopt lean on the
 * (x & ~m) / (x & m) decomposition, which Cbits cannot fold). TU-scoped. */
#include "axioms_apply_mask.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	requires range_ordering(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->mask;

	ensures umin64:     mask == _64_BIT_MASK ==> rv->u.min == \old(rv->u.min);
	ensures umax64:     mask == _64_BIT_MASK ==> rv->u.max == \old(rv->u.max);
	// SINGLE CONTRACT OF RECORD (fixed semantics): optimal masking widens iff
	// the range STRADDLES a block boundary (the bounds' 2^32-quotients
	// differ); a range wholly in one block keeps its tight masked form.
	// Stated in DIV terms, not & ~mask: the complement-mask terms seeded the
	// ApplyMaskBlocks axioms' e-matching in every consumer TU and tipped
	// eval_alu cliff stones (2026-07-28); quotients are built-in arithmetic.
	// land_block_div_u32 bridges to the body's & ~mask branch test. Under
	// --no-fixes ukeep32 goes red on high-block ranges -- documenting the
	// upstream over-widening FIX_APPLY_MASK_OPT repairs.
	ensures uwiden32:   mask == _32_BIT_MASK &&
		\old(rv->u.min) / (mask + 1) != \old(rv->u.max) / (mask + 1)
	 	==> rv->u.min == 0 && rv->u.max == mask;
	ensures ukeep32:    mask == _32_BIT_MASK &&
		\old(rv->u.min) / (mask + 1) == \old(rv->u.max) / (mask + 1)
	 	==> rv->u.min == (\old(rv->u.min) & mask) && rv->u.max == (\old(rv->u.max) & mask);
	ensures mask_set:   rv->mask == mask;
	ensures mask_ok:    rv->mask == _32_BIT_MASK || rv->mask == _64_BIT_MASK;
	ensures smin32:     mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN || rv->s.min == \old(rv->s.min);
	ensures smax32:     mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX || rv->s.max == \old(rv->s.max);
	ensures smin64:     mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN || rv->s.min == \old(rv->s.min);
	ensures smax64:     mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX || rv->s.max == \old(rv->s.max);
	ensures unchanged_v:    rv->v == \old(rv->v);
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
	ensures agree_min: \old(range_agreement(rv, mask)) &&
			\old(range_within_width(rv, mask))
			==> min_agreement(rv, mask);
	ensures agree_max: \old(range_agreement(rv, mask)) &&
			\old(range_within_width(rv, mask))
			==> max_agreement(rv, mask);
	ensures usound:     eval_apply_mask_unsigned_soundness(\old(*rv), *rv, mask);
	ensures ssound:     eval_apply_mask_signed_soundness(\old(*rv), *rv, mask);

	// OP-OPTIMALITY (apply_mask-optimal). PER-TRACK, mirroring the per-track
	// soundness above: unlike the binary operators these predicates quantify the
	// witness over ONE track's range only, no cross-track un_witness obligation, so
	// apply_mask needs NO self_optimal precondition -- the endpoint is its own
	// witness by construction.
	//
	// u track (FIX_APPLY_MASK_OPT): masking is modular reduction, so the masked
	// range is TIGHT whenever both bounds share a block above the mask; only a
	// STRADDLING range masks to a set spanning the 0/mask seam, where [0,mask] is
	// itself op-optimal (the boundary multiple attains 0, boundary-1 attains mask).
	// [Corrects the earlier note: straddle is NOT "genuinely loose" -- top IS the
	// best interval there. What was loose was the upstream widening of a range lying
	// wholly in a HIGH block, e.g. [mask+4, mask+6] -> tight [3,5]; the body fix
	// widens on block-mismatch instead.] So with the fix uopt is UNCONDITIONAL;
	// without it the old "no masking needed" guard stands.
	//
	// s track: eval_smax_bound(&rt) loads rt.s with the width's [INT_MIN, INT_MAX]
	// and the code widens iff the signed range escapes it. The signed masking has
	// the SAME over-widening (a range wholly in a high block masks to a tight low
	// interval yet is widened here), but its optimal test is the OFFSET sawtooth
	// boundary (jumps where v == 2^31 mod 2^32, not at multiples of 2^32) and it is
	// coupled to smin32/smax32/ssound/swidth -- so it is deliberately NOT fixed in
	// this pass; sopt keeps its within-width guard pending a careful signed pass.
	// Compile-gated like eval_and/eval_mul's optimality (2026-07-21): the
	// unconditional uopt injects a bare existential at every call site, and
	// in eval_alu's TU that tipped two margin-zero cliff stones (sx_vld32,
	// ord_dk) into 20-minute spins while proving nothing they need. The
	// dedicated PROVE_OPTIMALITY cell proves these clauses; consumer TUs
	// never see them.
#ifdef PROVE_OPTIMALITY
	ensures uopt: eval_apply_mask_unsigned_optimal(\old(*rv), *rv, mask);
	ensures sopt: \old(signed_range_within_width(rv, mask))
			==> eval_apply_mask_signed_optimal(\old(*rv), *rv, mask);
#endif
*/
void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask)
{
	struct bpf_reg_val rt;

	/* Bridge stones (land_block_div_u32 instances): convert the contract's
	 * div-form block test to the & ~mask form the branch and the block
	 * axioms speak. TU-local; consumers only ever see the div form. */
	/*@ assert blk_div_min: mask == _32_BIT_MASK ==>
	      (rv->u.min & 0xFFFFFFFF00000000) ==
	      0x100000000 * (rv->u.min / 0x100000000); */
	/*@ assert blk_div_max: mask == _32_BIT_MASK ==>
	      (rv->u.max & 0xFFFFFFFF00000000) ==
	      0x100000000 * (rv->u.max / 0x100000000); */

	rt.u.min = rv->u.min & mask;
	rt.u.max = rv->u.max & mask;

#ifdef FIX_APPLY_MASK_OPT
	/*
	 * Optimal masking (unsigned): masking is modular reduction mod (mask+1), so the
	 * masked range is TIGHT exactly when both bounds share a block above the mask
	 * (equal high bits, rv->u.min & ~mask == rv->u.max & ~mask). Only a range that
	 * STRADDLES a block boundary masks to a set spanning the 0/mask seam, where
	 * [0,mask] is op-optimal. The upstream test widened on ANY masking change,
	 * over-widening a range lying wholly in a high block ([mask+4, mask+6] masks to
	 * the tight [3,5]). Compare high bits instead. (64-bit mask: ~mask == 0, so both
	 * sides are 0 -> never widens, masking is the identity.)
	 */
	if ((rv->u.min & ~mask) != (rv->u.max & ~mask)) {
		rv->u.min = 0;
		rv->u.max = mask;
	} else {
		rv->u.min = rt.u.min;
		rv->u.max = rt.u.max;
	}
#else
	if (rt.u.min != rv->u.min || rt.u.max != rv->u.max) {
		rv->u.max = RTE_MAX(rt.u.max, mask);
		rv->u.min = 0;
	}
#endif

	eval_smax_bound(&rt, mask);

	#ifdef FIX_APPLY_MASK_SIGNED
		/* Fixed */
		if (rv->s.min < rt.s.min || rv->s.max > rt.s.max) {
			/* signed range escapes the width → low bits unknown → widen */
			rv->s.min = rt.s.min;              // INT_MIN_w
			rv->s.max = rt.s.max;              // INT_MAX_w
		}
	#else
		/* Original */
		rv->s.max = RTE_MIN(rt.s.max, rv->s.max);
		rv->s.min = RTE_MAX(rt.s.min, rv->s.min);
	#endif

	rv->mask = mask;

	/*
	 * OP-OPTIMALITY stones. Both tracks reduce to the same shape: under the
	 * guard the widening branch does not fire, the endpoints survive
	 * unchanged, and each endpoint witnesses ITSELF (the per-track predicates
	 * need no cross-track witness, so there is no bin_witness step here).
	 */
	/* u: masking is the identity on a range that already fits, which is what
	 * makes the `rt.u != rv->u` widening test false. */
	/*@ check uopt_id_min:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.min,Pre) & mask) == \at(rv->u.min,Pre); */
	/*@ check uopt_id_max:
	      \at(rv->u.max,Pre) <= mask ==>
	        (\at(rv->u.max,Pre) & mask) == \at(rv->u.max,Pre); */
	/*@ check uopt_keep:
	      \at(rv->u.max,Pre) <= mask ==>
	        rv->u.min == \at(rv->u.min,Pre) && rv->u.max == \at(rv->u.max,Pre); */
#ifdef FIX_APPLY_MASK_OPT
	/* Keep-branch ground facts under the block test (any same-block range, not
	 * only fits-under-mask): the stored endpoints are the masked Pre endpoints,
	 * ordered by land_block_range_u32; each is attained by its own Pre endpoint
	 * (the identity witnesses the existential directly). */
	/*@ assert uopt_keep_blk: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) ==
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        rv->u.min == (\at(rv->u.min,Pre) & mask) &&
	        rv->u.max == (\at(rv->u.max,Pre) & mask); */
	/* Straddle-case uopt witnesses (32-bit mask only; ~mask64 == 0 cannot
	 * straddle). B := the high block of the Pre u.max. Under a straddle:
	 * umin < B (block mono + gap + split), B <= umax (split), B & mask == 0
	 * (blockzero), and (B-1) & mask == mask (predtop; B >= 2^32 by the gap
	 * over umin's non-negative block). The branch pinned the outputs to
	 * [0, mask]: B attains u.min == 0 and B-1 attains u.max == mask -- the
	 * two ground instances the predicate existentials need. */
	/*@ assert uopt_str_out: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        rv->u.min == 0 && rv->u.max == mask; */
	/*@ assert uopt_str_zero: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        \at(rv->u.min,Pre) <= (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) <=
	        \at(rv->u.max,Pre) &&
	        ((\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) & mask) == 0; */
	/*@ assert uopt_str_top: mask == _32_BIT_MASK &&
	      (\at(rv->u.min,Pre) & 0xFFFFFFFF00000000) !=
	      (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) ==>
	        \at(rv->u.min,Pre) <= (\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) - 1 &&
	        (((\at(rv->u.max,Pre) & 0xFFFFFFFF00000000) - 1) & mask) == mask; */
#endif

	/* s: rt.s holds the width's [INT_MIN, INT_MAX] after eval_smax_bound, so a
	 * within-width signed range fails the escape test and is kept; the
	 * re-encode/decode round-trip on a canonical endpoint is the identity
	 * (to_signed_canon_rt). */
	/*@ assert sopt_keep:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        rv->s.min == \at(rv->s.min,Pre) && rv->s.max == \at(rv->s.max,Pre); */
	/*@ assert sopt_rt_max:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.max,Pre)) & mask, mask)
	          == \at(rv->s.max,Pre); */
	/*@ assert sopt_rt_min:
	      \at(signed_range_within_width(rv, mask),Pre) ==>
	        to_signed(((uint64_t)\at(rv->s.min,Pre)) & mask, mask)
	          == \at(rv->s.min,Pre); */
}


