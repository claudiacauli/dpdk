#ifndef EVAL_APPLY_MASK_H
#define EVAL_APPLY_MASK_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
// Value-tracking soundness: any concrete value the register could hold
// before masking is still covered by the tracked ranges afterwards.
// Single operand, so the uint64 cast is non-negative and plain & works
// (no wrap_diff needed — cf. eval_sub.h).
predicate eval_apply_mask_unsigned_soundness(struct bpf_reg_val od,
                                             struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x;
		od.u.min <= x <= od.u.max
			==> nw.u.min <= (x & msk) <= nw.u.max;

predicate eval_apply_mask_signed_soundness(struct bpf_reg_val od,
                                           struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v;
		od.s.min <= v <= od.s.max
			==> nw.s.min <= to_signed(((uint64_t)v) & msk, msk) <= nw.s.max;
*/

void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask);

#endif
