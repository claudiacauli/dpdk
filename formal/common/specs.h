#ifndef SPECS_H
#define SPECS_H

#include "shared.h"

/*@
predicate unsigned_range_ordering(struct bpf_reg_val *rv) =
	rv->u.min <= rv->u.max;

predicate signed_range_ordering(struct bpf_reg_val *rv) =
	rv->s.min <= rv->s.max;

predicate range_ordering(struct bpf_reg_val *rv) =
	unsigned_range_ordering(rv) && signed_range_ordering(rv);

// The register is "sign-determinate": the tracked ranges pin down which
// side of the sign boundary the value lives on.
predicate sign_determinate(struct bpf_reg_val *rv, uint64_t mask) =
	rv->s.min >= 0 || rv->s.max < 0 ||
	rv->u.min > (mask>>1) || rv->u.max <= (mask>>1);

predicate min_sign_consistency(struct bpf_reg_val *rv, uint64_t mask) =
	sign_determinate(rv, mask) ==>
		rv->u.min == ((uint64_t)rv->s.min & mask);

predicate max_sign_consistency(struct bpf_reg_val *rv, uint64_t mask) =
	sign_determinate(rv, mask) ==>
		rv->u.max == ((uint64_t)rv->s.max & mask);

predicate range_sign_consistency(struct bpf_reg_val *rv, uint64_t mask) =
	min_sign_consistency(rv, mask) && max_sign_consistency(rv, mask);

predicate range_validity(struct bpf_reg_val *rv, uint64_t mask) =
	rv->v.type == RTE_BPF_ARG_UNDEF ||
	(range_ordering(rv) && range_sign_consistency(rv, mask));

predicate unsigned_range_within_width(struct bpf_reg_val *rv, uint64_t mask) =
	rv->u.max <= mask;

predicate signed_range_within_width(struct bpf_reg_val *rv, uint64_t mask) =
	-(int64_t)(mask>>1) - 1 <= rv->s.min &&
	rv->s.max <= (int64_t)(mask>>1);

predicate range_within_width(struct bpf_reg_val *rv, uint64_t mask) =
	unsigned_range_within_width(rv, mask) && signed_range_within_width(rv, mask);
*/

//@ predicate is_scalar(integer t) = t == RTE_BPF_ARG_RAW;
/*@ predicate is_pointer(integer t) =
		t == RTE_BPF_ARG_PTR || t == RTE_BPF_ARG_PTR_MBUF ||
		t == RTE_BPF_ARG_RESERVED;
*/
//@ predicate is_scalar_or_pointer(integer t) = is_scalar(t) || is_pointer(t);

/*@
// AND can only clear bits, so `x & msk` is bounded by the mask.
// Cbits has no bounds axiom for land, so SMT can't derive this;
// trusted (same family as the land axioms in eval_apply_mask.c).
axiomatic LandMaskBound {
	axiom land_le_mask:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x & y) <= y;
	// Masking with an all-ones low mask is the identity for values
	// that already fit under it (i.e. no bits get cleared). Trusted;
	// same as land_uint{32,64}_max in eval_apply_mask.c.
	axiom land_id_u64:
		\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x;
	axiom land_id_u32:
		\forall integer x; 0 <= x <= 0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x;
}
*/

/*@
axiomatic BpfArgPtrType {
// The 0x10 (RTE_BPF_ARG_PTR) bit is never set on the two scalar
// enumerators. Trusted: WP's integer model cannot discharge
// bitwise-AND facts through the SMT provers (Cbits limitation).
axiom ptr_flag_excludes_scalars:
	\forall integer t;
		(t & RTE_BPF_ARG_PTR) != 0 ==>
		t != RTE_BPF_ARG_UNDEF && t != RTE_BPF_ARG_RAW;
// Conversely, a clear 0x10 bit rules out the three pointer-kind
// enumerators (each of which has that bit set).
axiom no_ptr_flag_excludes_pointers:
	\forall integer t;
		(t & RTE_BPF_ARG_PTR) == 0 ==>
		t != RTE_BPF_ARG_PTR && t != RTE_BPF_ARG_PTR_MBUF &&
		t != RTE_BPF_ARG_RESERVED;
}
*/


//@ lemma land_comm: \forall integer x, y; (x & y) == (y & x);

/*
 * WP's Cbits theory only knows `x & -1 == x` for the *mathematical*
 * integer -1 (axiom land_1bis) and has no bit-level extensionality
 * axiom, so the 64-bit variant `x & 0xFFFFFFFFFFFFFFFF == x` is not a
 * first-order consequence of the shipped axioms and no SMT solver can
 * derive it. We supply it as a trusted axiom: masking with all 64 bits
 * set is the identity on values in [0, 2^64 - 1]. (This is the same
 * fact as land_1bis restricted to 64-bit unsigned values; it is
 * provable from land_extraction + bit extensionality in WP's Coq
 * model, just not in the first-order SMT encoding.)
 */
/*@
axiomatic LandUint64AllOnes {
	axiom land_uint64_max:
	\forall integer x;
	0 <= x <= 0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x;
}

axiomatic LandUint32AllOnes {
	axiom land_uint32_max:
	\forall integer x;
	0 <= x <= 0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x;
}
*/

/*
 * Same story for monotonicity: Cbits has no bounds axiom for land, so
 * `(x & y) <= x` for non-negative x, y (AND can only clear bits) is
 * also unprovable by SMT. Trusted axiom, again true in the intended
 * bitwise model.
 */
/*@
axiomatic LandBounds {
	axiom land_nonneg_le:
	\forall integer x, y;
	0 <= x && 0 <= y ==> 0 <= (x & y) <= x;
}
*/

/*
 * Single wrap of a masked sum: for x in (mask, 2*mask], (x & mask) == x - (mask+1).
 * Same Cbits limitation as the other land_* axioms (WP can't fold `&`); CBMC-checked.
 */
/*@
axiomatic LandWrap {
	axiom land_wrap_u32:
		\forall integer x; 0xFFFFFFFF < x <= 2*0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x - 0x100000000;
	axiom land_wrap_u64:
		\forall integer x;
		0xFFFFFFFFFFFFFFFF < x <= 2*0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x - 0x10000000000000000;
}
*/

/*
 * Top-of-range wrap for the 32-bit mask: for x in the last 2^32-sized
 * block of the uint64 domain, [2^64 - 2^32, 2^64), the masked value is
 * (x & 0xFFFFFFFF) == x - (2^64 - 2^32). This is the case that
 * land_id_u32/land_wrap_u32 do not reach: uint64 sums of uint64-cast
 * negative int32-canonical bounds land exactly there. Same Cbits
 * limitation as the rest of the land_* family; trusted, CBMC-checked
 * over the full uint64 domain.
 */
/*@
axiomatic LandWrapTop {
	axiom land_wrap_u32_top:
		\forall integer x;
		0xFFFFFFFF00000000 <= x <= 0xFFFFFFFFFFFFFFFF ==>
		(x & 0xFFFFFFFF) == x - 0xFFFFFFFF00000000;
}
*/

/*@
// Sign-extended (canonical) value of a w-bit pattern v, for msk = 2^w - 1.
// Single shared definition, used by the eval_* soundness predicates.
logic integer to_signed(integer v, integer msk) =
      v <= (msk >> 1) ? v : v - (msk + 1);

// Operand width in bits for the two supported masks (shift-amount bound).
logic integer op_bits(integer msk) =
      msk == _32_BIT_MASK ? 32 : 64;
*/

/*
 * Variable-amount shifts are nonlinear (x << y == x * 2^y), so WP's SMT
 * back-ends cannot reason about them: even `u.min <= u.max` after a shift
 * is out of reach. Same remedy as the land_* family — trusted axioms
 * giving the linear facts the solvers need. All CBMC-checked over the full
 * domain (x in [0,2^64), shift in [0,64), products modelled in __int128).
 * Non-negative operands only, which is all the eval_* shift paths use.
 */
/*@
axiomatic LenShift {
	axiom lsl_nonneg:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x << y);
	axiom lsl_val_mono:
		\forall integer a, b, y;
		0 <= a <= b && 0 <= y ==> (a << y) <= (b << y);
	axiom lsl_amt_mono:
		\forall integer x, p, q;
		0 <= x && 0 <= p <= q ==> (x << p) <= (x << q);
	// Combined monotonicity: triggers on the two shift terms that actually
	// occur (min<<min-shift, max<<max-shift) with no synthesised
	// intermediate, so e-matching can fire it directly.
	axiom lsl_both_mono:
		\forall integer a, b, p, q;
		0 <= a <= b && 0 <= p <= q ==> (a << p) <= (b << q);
	axiom lsl_width_bound:
		\forall integer x, k, w;
		0 <= k <= w && 0 <= x && x <= (1 << (w - k)) - 1
		==> (x << k) <= (1 << w) - 1;
	axiom lsr_shrink:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x >> y) <= x;
	axiom lsr_val_mono:
		\forall integer a, b, y;
		0 <= a <= b && 0 <= y ==> (a >> y) <= (b >> y);
	axiom lsr_amt_anti:
		\forall integer x, p, q;
		0 <= x && 0 <= p <= q ==> (x >> q) <= (x >> p);
	// Combined anti-monotonicity, the lsr twin of lsl_both_mono: after
	// eval_rsh the POs contain exactly (min >> max-shift) and
	// (max >> min-shift); composing lsr_val_mono with lsr_amt_anti would
	// need the intermediate term (max >> max-shift), which never occurs,
	// so e-matching cannot chain them.
	axiom lsr_both_anti:
		\forall integer a, b, p, q;
		0 <= a <= b && 0 <= p <= q ==> (a >> q) <= (b >> p);
	// Machine-form width bound, mask-concrete so no free variable needs
	// instantiating: the guard term matches RTE_LEN2MASK's exact PO shape
	// `(2^64-1) >> (64-(opsz-k))`, and the conclusion is the literal mask.
	// (The 64-bit all-ones literal is deliberate — that is the term WP
	// emits for RTE_LEN2MASK, so the trigger fires.)
	axiom lsl_width_32:
		\forall integer x, k;
		0 <= k && k < 32 &&
		0 <= x && x <= (0xFFFFFFFFFFFFFFFF >> (64 - (32 - k)))
		==> (x << k) <= 0xFFFFFFFF;
	axiom lsl_width_64:
		\forall integer x, k;
		0 <= k && k < 64 &&
		0 <= x && x <= (0xFFFFFFFFFFFFFFFF >> (64 - (64 - k)))
		==> (x << k) <= 0xFFFFFFFFFFFFFFFF;
	// Signed-branch support (eval_lsh). All CBMC-checked over the full
	// domain (axiom_validation/validate_specs_axioms.c, as is the whole
	// axiomatic).
	// The sign guard `(uint64_t)s.min >> (opsz-1) == 0` implies
	// s.min >= 0: a negative int64 wraps to >= 2^63 under to_uint64, and
	// 2^63 >> w != 0 for any w <= 63. The shift amount w is kept
	// SYMBOLIC on purpose: with a constant amount Qed normalises
	// `(x >> 31) == 0` into a `land(-2^31, x) == 0` bitmask test, which
	// no longer matches the goal's `lsr(to_uint64(s.min), opsz-1) == 0`
	// term, and the axiom can never fire. Quantifying over int64_t bakes
	// the +2^64 wrap into the axiom (the provers time out re-deriving it
	// from to_uint64's recursive definition).
	axiom lsr_sign_any:
		\forall int64_t v; \forall integer w;
		31 <= w <= 63 && (((uint64_t)v) >> w) == 0 ==> 0 <= v;
	// RTE_LEN2MASK(n, int64_t) shows up as to_sint64(lsr(allones, 64-n));
	// with n <= 63 the shifted value is <= INT64_MAX, which lets the
	// provers strip the to_sint64 wrapper (id_sint64) and expose the bare
	// lsr term the width axioms below trigger on.
	axiom lsr_allones_sint:
		\forall integer k;
		1 <= k <= 63
		==> 0 <= (0xFFFFFFFFFFFFFFFF >> k) <= 0x7FFFFFFFFFFFFFFF;
	// 32-bit refinement of the same shape: the signed guard's
	// RTE_LEN2MASK(32 - u.max - 1, int64_t) term has shift amounts
	// >= 33, pinning the bound (and hence s.max, and hence v <= s.max in
	// the soundness quantifier) under 2^31 so the land_*_u32 identity
	// axioms can fire. lsr_amt_anti cannot substitute: its conclusion
	// would need the ground term `allones >> 33`, which never occurs in
	// the POs.
	axiom lsr_allones_33:
		\forall integer k;
		33 <= k <= 63
		==> (0xFFFFFFFFFFFFFFFF >> k) <= 0x7FFFFFFF;
	// Signed width bounds, mask-concrete like lsl_width_32/64. The
	// hypothesis is written in the exact shape of the signed overflow
	// guard `s.max < RTE_LEN2MASK(opsz - u.max - 1, int64_t)`, i.e.
	// strict `<` against `allones >> (64 - (W - k - 1))` = 2^(W-k-1)-1,
	// so x <= 2^(W-k-1)-2 and x*2^k <= 2^(W-1) - 2^(k+1) < 2^(W-1).
	axiom lsl_swidth_32:
		\forall integer x, k;
		0 <= k && k <= 30 &&
		0 <= x && x < (0xFFFFFFFFFFFFFFFF >> (64 - (32 - k - 1)))
		==> (x << k) <= 0x7FFFFFFF;
	axiom lsl_swidth_64:
		\forall integer x, k;
		0 <= k && k <= 62 &&
		0 <= x && x < (0xFFFFFFFFFFFFFFFF >> (64 - (64 - k - 1)))
		==> (x << k) <= 0x7FFFFFFFFFFFFFFF;
}

// Ground values of the two mask half-shifts, i.e. msk >> 1 for the two
// supported masks. NOT trusted axioms: WP proves both by Qed constant
// folding. They are stated so the equations also exist in POs where msk
// stays SYMBOLIC (e.g. the monolithic usound/ssound goals): there Qed
// cannot fold lsr(msk, 1) per mask case, the provers have no evaluation
// axioms for lsr on literals, and to_signed's branch condition becomes
// undecidable without them.
lemma lsr_half_32: (0xFFFFFFFF >> 1) == 0x7FFFFFFF;
lemma lsr_half_64: (0xFFFFFFFFFFFFFFFF >> 1) == 0x7FFFFFFFFFFFFFFF;
*/

#endif /* SPECS_H */
