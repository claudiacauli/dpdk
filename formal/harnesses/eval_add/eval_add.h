#ifndef EVAL_ADD_H
#define EVAL_ADD_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
predicate eval_add_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= ((x + y) & msk) <= nw.u.max;

// to_signed comes from common/specs.h

predicate eval_add_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.s.min <= to_signed((x + y) & msk, msk) <= nw.s.max;

// OP-OPTIMALITY (add-optimal). Each output endpoint is ATTAINED by a
// representable input PAIR (bin_witness) -- the best abstract transformer on
// endpoints. PRELIMINARY (optimality_notes.md); holds from SELF-OPTIMAL
// operands in the no-overflow regime (guard stated in the .c contract).
predicate eval_add_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x + y) & msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x + y) & msk) == nw.u.min);

predicate eval_add_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                  struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && to_signed((x + y) & msk, msk) == nw.s.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && to_signed((x + y) & msk, msk) == nw.s.min);

*/


void eval_add(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk);

#endif
