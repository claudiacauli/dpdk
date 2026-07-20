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

// OP-OPTIMALITY (apply_mask-optimal). Each output endpoint is ATTAINED by a
// representable input (per-track, mirroring the per-track soundness above).
// PRELIMINARY (optimality_notes.md); op-optimal from a SELF-OPTIMAL input in
// the non-straddle regime (64-bit mask = identity, or 32-bit range that fits);
// a range straddling a 2^32 boundary widens u to [0,mask] and is loose.
predicate eval_apply_mask_unsigned_optimal(struct bpf_reg_val od,
                                           struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x; od.u.min <= x <= od.u.max && (x & msk) == nw.u.max) &&
	(\exists integer x; od.u.min <= x <= od.u.max && (x & msk) == nw.u.min);

predicate eval_apply_mask_signed_optimal(struct bpf_reg_val od,
                                         struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer v; od.s.min <= v <= od.s.max && to_signed(((uint64_t)v) & msk, msk) == nw.s.max) &&
	(\exists integer v; od.s.min <= v <= od.s.max && to_signed(((uint64_t)v) & msk, msk) == nw.s.min);
*/

void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask);

#endif
