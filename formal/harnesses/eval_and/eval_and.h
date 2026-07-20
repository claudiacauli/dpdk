#ifndef EVAL_AND_H
#define EVAL_AND_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_and_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk)
			==> nw.s.min <= to_signed(v & y, msk) <= nw.s.max;

predicate eval_and_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= (x & y) <= nw.u.max;

// OP-OPTIMALITY (unsigned). Both output endpoints are ATTAINED by a
// representable operand pair. Same shape as the Category-A ops; what differs
// is the GUARD in eval_and.c, which is far narrower because the bit-fill
// bound is usually loose (optimality_notes.md §6d).
predicate eval_and_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && (x & y) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && (x & y) == nw.u.min);

// OP-OPTIMALITY (signed). Mirrors the unsigned form, but the attained quantity
// is the CANONICAL reading of the AND, matching eval_and_signed_soundness.
predicate eval_and_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                   struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk)
	                       && to_signed(x & y, msk) == nw.s.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk)
	                       && to_signed(x & y, msk) == nw.s.min);
*/

void eval_and(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_AND_H */
