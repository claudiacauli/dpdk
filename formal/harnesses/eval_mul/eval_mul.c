#include "eval_mul.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
#include "axioms_mul.h"
#include "../../common/axioms_and.h"

/*
 * Masked product of two unsigned operands, stated in the MATH-product form
 * eval_mul_unsigned_soundness uses. The body computes the C uint64 product
 * (which wraps mod 2^64 before masking), so the uint-wrap-vs-math bridge
 * mul_mask_wrap is discharged HERE, in this one VC; callers see only the
 * `(a*b) & msk` ensures. That keeps the bridge's uint-product trigger out
 * of every usound goal — inline, the constants branch's masked uint
 * product is in scope for all goals and perturbs them. Not fix-gated: the
 * unsigned constants branch is identical in both semantics, and this is a
 * pure extraction of `(rd->u.min * rs->u.min) & msk`.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	assigns \nothing;
	ensures \result == ((a * b) & msk);
*/
static uint64_t mul_umask(uint64_t a, uint64_t b, uint64_t msk)
{
	return (a * b) & msk;
}

#ifdef FIX_MUL_SCONST
/*
 * Sign-extend the low-opsz-bit pattern p (in [0, msk]) to its signed
 * value — the C computation of to_signed(p, msk). For msk = 2^w - 1,
 * p <= msk>>1 keeps p; otherwise p - (msk + 1). msk + 1 wraps to 0 for
 * the 64-bit mask, so (int64_t)(p - 0) == (int64_t)p correctly
 * reinterprets a set top bit as negative.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t mul_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}

/*
 * Sign-extended masked product of two signed operands, stated in the
 * MATH-product form the signed-soundness predicate uses. The body still
 * computes it the C way (uint64 product, then mask, then mul_sext), so the
 * uint-wrap-vs-math bridge to_signed_mul_wrap is discharged HERE, in this
 * one VC — the callers see only the `to_signed((d*e)&msk, msk)` ensures.
 * That keeps the bridge axiom's uint-product trigger out of eval_mul's
 * soundness goals entirely: left inline, that term (from the signed
 * constants branch) is in scope for every goal and the bidirectional
 * equality matching-loops, timing out even the trivial all-constant part.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	assigns \nothing;
	ensures \result == to_signed((d * e) & msk, msk);
*/
static int64_t mul_sext2(int64_t d, int64_t e, uint64_t msk)
{
	return mul_sext(((uint64_t)d * (uint64_t)e) & msk, msk);
}
#endif

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
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
	ensures usound:     eval_mul_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_mul_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (mul-optimal). Nonlinear but CORNER-based: on non-negatives the
	// product is monotone in both operands, so the corner products are the extremes
	// -- Category A, NOT B. Soundness above is UNCONDITIONAL.
	//
	// THE GUARDS MIRROR THE CODE'S OWN BRANCH CONDITIONS, and deliberately not the
	// weaker "the product fits" an earlier draft used. Those are NOT the same:
	// the code takes its fast path only when BOTH operands are below the half-width
	// bound, which is strictly stronger than the product fitting. With msk 2^64-1,
	// rd.u.max = 2^40 and rs.u.max = 2 the product 2^41 fits the width, yet
	// rd.u.max exceeds msk >> 32 so eval_umax_bound fires and the result is NOT
	// op-optimal. A "product <= msk" guard would therefore be false as stated --
	// the same trap eval_lsh's sopt guard fell into. Derive the guard from the
	// branch condition, never from the mathematical no-overflow condition.
	//
	// Both guards also cover the constants branch, which is exact (hence
	// op-optimal) and is tested first.
	//
	// GATED behind PROVE_OPTIMALITY (2026-07-20): the ~13 witness stones
	// these ensures need are `assert`s -- hypotheses of EVERY later PO --
	// and their nonlinear product / masked-product e-nodes multiply the
	// e-matching candidates for the mul axiom family inside every
	// usound/ssound split part (the documented §6l hazard: earlier stones
	// moved 75->70/77; these moved 77->58/61). The driver proves
	// uopt/sopt + stones in a dedicated -DPROVE_OPTIMALITY cell; the
	// soundness cell compiles without. BACKLOG C5 tracks the permanent
	// folded-lemma form (mirroring mul_usound/ssound_overflow).
#ifdef PROVE_OPTIMALITY
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.max) <= (msk >> (opsz / 2)) &&
		\old(rs->u.max) <= (msk >> (opsz / 2))
			==> eval_mul_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->s.min) >= 0 && \old(rs->s.min) >= 0 &&
		\old(rd->s.max) <= ((msk >> 1) >> (opsz / 2)) &&
		\old(rs->s.max) <= ((msk >> 1) >> (opsz / 2))
			==> eval_mul_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
#endif
*/
void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* Resolve opsz per mask up front: the guard shift `msk >> opsz/2`
	 * substitutes opsz -> op_bits(msk), which does not auto-fold; pinning
	 * opsz to a literal lets the guard bound collapse to 2^(w/2)-1. */
	/*@ assert ob32: msk == 0xFFFFFFFF ==> opsz == 32; */
	/*@ assert ob64: msk == 0xFFFFFFFFFFFFFFFF ==> opsz == 64; */
	/* msk is all-ones: lets land_allones_id (axioms_and.h) strip `& msk`
	 * from a product that fits the width — the soundness mask-strip — with
	 * the shape guard discharged by assumption (a symbolic land, not a
	 * ground one the provers must evaluate). Proved from shape_mask32/64. */
	/*@ assert msk_shape: (msk & (msk + 1)) == 0; */

	/* both operands are constants */
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		rd->u.min = mul_umask(rd->u.min, rs->u.min, msk);
		rd->u.max = mul_umask(rd->u.max, rs->u.max, msk);
	/* check for overflow */
#ifdef FIX_MUL_UGUARD
	/*
	 * Upstream tests `rs->u.max <= msk >> opsz`, not `>> opsz / 2` like
	 * the rd side. For opsz == 64 that is `msk >> 64` — shift-by-width
	 * UB that evaluates to msk on shift-masking hardware (x86/ARM), so
	 * the guard vanishes and the 64-bit product overflows; for
	 * opsz == 32 it is `msk >> 32 == 0`, making the fast path all but
	 * dead. Both operands must be < 2^(w/2) for the product to fit in w
	 * bits. BMC witness (upstream): opsz 64, rd.u.max 2^32-1,
	 * rs.u.max 2^32 -> product wraps, tracked u.max under-approximates.
	 */
	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz / 2) {
#else
	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz) {
#endif
		/*
		 * Stones for the nonlinear multiply, asserted here where only
		 * the guard + preconditions are in scope. u_nof: the guarded
		 * product fits in the width (mul_bound), so the C multiply's
		 * to_uint64 wrap is the identity; u_mono: monotonicity gives
		 * the new u.min <= u.max and bounds every witness product.
		 */
		/* per-mask so the msk==const hypothesis folds op_bits, /2 and the
		 * guard shift to a literal, letting mask-concrete mul_bound fire */
		/*@ assert u_nof32: msk == 0xFFFFFFFF ==>
		      (rd->u.max * rs->u.max) <= msk; */
		/*@ assert u_nof64: msk == 0xFFFFFFFFFFFFFFFF ==>
		      (rd->u.max * rs->u.max) <= msk; */
		/*@ assert u_mono: (rd->u.min * rs->u.min) <= (rd->u.max * rs->u.max); */
		rd->u.max *= rs->u.max;
		rd->u.min *= rs->u.min;
	} else
		eval_umax_bound(rd, msk);

	/* both operands are constants */
	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
#ifdef FIX_MUL_SCONST
		/*
		 * Upstream stores the raw masked product pattern in s.min/s.max
		 * without sign-extending: when the low-w product has its sign
		 * bit set (e.g. opsz == 32, 2^30 * 2 -> 0x80000000) the tracked
		 * value is a large positive instead of the true negative,
		 * breaking swidth and ssound. Sign-extend to the canonical
		 * signed value.
		 */
		rd->s.min = mul_sext2(rd->s.min, rs->s.min, msk);
		rd->s.max = mul_sext2(rd->s.max, rs->s.max, msk);
#else
		rd->s.min = ((uint64_t)rd->s.min * (uint64_t)rs->s.min) & msk;
		rd->s.max = ((uint64_t)rd->s.max * (uint64_t)rs->s.max) & msk;
#endif
	/* check that both operands are positive and no overflow */
#ifdef FIX_MUL_SGUARD
	/*
	 * Upstream has NO overflow guard here: `rd->s.max *= rs->s.max` on
	 * int64 overflows (signed-overflow UB for 64-bit; exceeds msk>>1 in
	 * every non-trivial case), so the tracked s.max leaves the signed
	 * width and range ordering can invert (ESBMC witness). Require both
	 * maxima below 2^((w-1)/2) so the product stays <= msk>>1:
	 * (msk>>1) >> (opsz/2) is 0x7FFF (opsz 32) / 0x7FFFFFFF (opsz 64),
	 * and B*B <= msk>>1 in both.
	 */
	} else if (rd->s.min >= 0 && rs->s.min >= 0 &&
			rd->s.max <= (msk >> 1) >> (opsz / 2) &&
			rs->s.max <= (msk >> 1) >> (opsz / 2)) {
#else
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
#endif
		/*@ assert s_nof32: msk == 0xFFFFFFFF ==>
		      (rd->s.max * rs->s.max) <= (msk >> 1); */
		/*@ assert s_nof64: msk == 0xFFFFFFFFFFFFFFFF ==>
		      (rd->s.max * rs->s.max) <= (msk >> 1); */
		/*@ assert s_mono: (rd->s.min * rs->s.min) <= (rd->s.max * rs->s.max); */
		rd->s.max *= rs->s.max;
		/*
		 * Frame stone for the second multiply's RTE overflow guard
		 * (rte_signed_overflow_4 timed out 2026-07-20): the guard's
		 * product e-node reads rs->s.min AFTER the s.max store, while
		 * the s_nof/s_mono chain above is stated on the PRE read, and
		 * the monolithic side-goal times out deriving the collapse
		 * itself. rs is \separated from rd, so the read is unchanged.
		 * Linear VC (select-over-store + separation), no product
		 * e-nodes — cannot perturb the soundness splits.
		 */
		/*@ assert s_frame: rs->s.min == \at(rs->s.min, Pre); */
		rd->s.min *= rs->s.min;
	} else
		eval_smax_bound(rd, msk);

#ifdef PROVE_OPTIMALITY
	/*
	 * OP-OPTIMALITY stones. On non-negatives the product is monotone in BOTH
	 * operands, so the corners are UNCROSSED: u.max <- (rd.u.max, rs.u.max),
	 * u.min <- (rd.u.min, rs.u.min). self_optimal supplies the corner
	 * un_witnesses that form each bin_witness; the _sum_ stones say those
	 * corner products are exactly the stored endpoints, which needs the
	 * guarded no-overflow (the u_nof and s_nof stones above) to strip `& msk`.
	 * The u track needs no frame step: nothing in the signed block writes
	 * rd->u (eval_smax_bound assigns only rv->s).
	 *
	 * The whole block is gated with the uopt/sopt ensures: these asserts'
	 * nonlinear product e-nodes are assumed into every soundness PO and
	 * were diagnosed as what pushed the usound/ssound split tails past
	 * the ceiling (see the contract comment). u_nof/s_nof above are NOT
	 * gated -- they predate optimality and serve the soundness proof.
	 */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.max,Pre) <= (msk >> (opsz / 2)) &&
	      \at(rs->u.max,Pre) <= (msk >> (opsz / 2)) ==>
	        ((\at(rd->u.max,Pre) * \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.max,Pre) <= (msk >> (opsz / 2)) &&
	      \at(rs->u.max,Pre) <= (msk >> (opsz / 2)) ==>
	        ((\at(rd->u.min,Pre) * \at(rs->u.min,Pre)) & msk) == rd->u.min; */

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
	/* Bridge the two representations. The optimality WITNESS is a PATTERN
	 * (((uint64_t)s.max) & msk), but the constants branch computes via
	 * mul_sext2 on CANONICAL values and the fast branch multiplies the
	 * canonical s fields directly. Under the guard both endpoints are
	 * non-negative and within width, so the encoding is the identity and the
	 * two forms coincide -- stating that once collapses the pattern layer out
	 * of the _sum_ goals below. */
	/*@ assert sopt_pat_id:
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.max,Pre)) & msk) == \at(rd->s.max,Pre) &&
	        (((uint64_t)\at(rs->s.max,Pre)) & msk) == \at(rs->s.max,Pre); */
	/* PER-MASK, following the u_nof/s_nof precedent above: pinning msk to a
	 * literal folds op_bits, the /2 and the guard shift into constants, so the
	 * B*B <= msk>>1 bound the mask-strip needs becomes ground arithmetic. The
	 * mask-symbolic form of this stone proves only 75/77 split parts, and
	 * (measured) adding post-merge no-overflow stones to help it made it WORSE,
	 * 70/77 -- extra hypotheses enlarge the nonlinear search. smin needs no such
	 * split: its product is dominated by smax's via s_mono. */
	/*@ assert sopt_sum_smax32:
	      msk == 0xFFFFFFFF &&
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smax64:
	      msk == 0xFFFFFFFFFFFFFFFF &&
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin:
	      \at(rd->s.min,Pre) >= 0 && \at(rs->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) &&
	      \at(rs->s.max,Pre) <= ((msk >> 1) >> (opsz / 2)) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) *
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
#endif
}
