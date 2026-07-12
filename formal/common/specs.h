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

#include "axioms.h"

#endif /* SPECS_H */
