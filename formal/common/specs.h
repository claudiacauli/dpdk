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
*/

#endif /* SPECS_H */
