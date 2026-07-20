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

predicate min_agreement(struct bpf_reg_val *rv, uint64_t mask) =
	sign_determinate(rv, mask) ==>
		rv->u.min == ((uint64_t)rv->s.min & mask);

predicate max_agreement(struct bpf_reg_val *rv, uint64_t mask) =
	sign_determinate(rv, mask) ==>
		rv->u.max == ((uint64_t)rv->s.max & mask);

predicate range_agreement(struct bpf_reg_val *rv, uint64_t mask) =
	min_agreement(rv, mask) && max_agreement(rv, mask);

// Scalar-only scope (per Marat): the UNDEF escape is dropped — every
// register reaching an operator is a defined scalar, so validity is just
// ordering + agreement. The dispatcher guards its register-file invariant
// with an explicit is_scalar(...) ==> instead.
predicate range_validity(struct bpf_reg_val *rv, uint64_t mask) =
	range_ordering(rv) && range_agreement(rv, mask);

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

#include "axioms.h"

/*@
// INTERSECTION-soundness witness (Marat's weaker form). A register denotes
// the values in BOTH tracks: a pattern p with u.min<=p<=u.max AND its signed
// reading s.min<=to_signed(p)<=s.max. Quantifying soundness over this set is
// op(gamma(in)) subseteq gamma(out) with gamma = the intersection — it makes
// range_agreement unnecessary for soundness, since the disagreeing patterns
// agreement used to exclude are simply outside the quantifier's range.
predicate un_witness(struct bpf_reg_val od, integer x, uint64_t mask) =
	od.u.min <= x <= od.u.max &&
	od.s.min <= to_signed(x, mask) <= od.s.max;

predicate bin_witness(struct bpf_reg_val od, struct bpf_reg_val os,
                      integer x, integer y, uint64_t mask) =
	un_witness(od, x, mask) && un_witness(os, y, mask);

// SELF-OPTIMALITY (input optimality). A register is self-optimal when each of
// its four range endpoints is itself attained by a representable value -- i.e.
// the ranges are the TIGHTEST abstraction of its OWN value set, not a loose
// over-approximation of it. It is the natural precondition for propagating
// OP-OPTIMALITY through an operator: no operator can recover an op-optimal
// output from a self-suboptimal input (two concrete sets with the same range
// endpoints but different interiors are indistinguishable to the operator).
// In Abstract Interpretation terms this is a REDUCED element -- a fixpoint of
// the reduced-product reduction alpha.gamma over our two interval tracks
// (unsigned + signed); a domain where every element is self-optimal would be a
// Galois insertion. PRELIMINARY -- introduced during the eval_neg optimality
// study (2026-07, see optimality_notes.md); whether every operator needs and
// preserves self-optimality is still under evaluation across the other ops.
predicate self_optimal(struct bpf_reg_val rv, uint64_t msk) =
	un_witness(rv, rv.u.min, msk) &&
	un_witness(rv, rv.u.max, msk) &&
	un_witness(rv, (uint64_t)rv.s.min & msk, msk) &&
	un_witness(rv, (uint64_t)rv.s.max & msk, msk);
*/

#endif /* SPECS_H */
