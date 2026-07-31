#ifndef EVAL_APPLY_MASK_H
#define EVAL_APPLY_MASK_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
predicate eval_apply_mask_unsigned_soundness(struct bpf_reg_val od,
                                             struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x;
		0 <= x <= od.mask && un_witness(od, x, od.mask)
			==> nw.u.min <= (x & msk) <= nw.u.max;

predicate eval_apply_mask_signed_soundness(struct bpf_reg_val od,
                                           struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x;
		0 <= x <= od.mask && un_witness(od, x, od.mask)
			==> nw.s.min <= to_signed(x & msk, msk) <= nw.s.max;

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
