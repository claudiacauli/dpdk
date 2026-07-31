#ifndef EVAL_ADD_H
#define EVAL_ADD_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "../../common/semantics.h"

/*@
predicate eval_add_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= SEM_ADD(x, y, msk) <= nw.u.max;

predicate eval_add_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.s.min <= to_signed(SEM_ADD(x, y, msk), msk) <= nw.s.max;

predicate eval_add_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && SEM_ADD(x, y, msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && SEM_ADD(x, y, msk) == nw.u.min);

predicate eval_add_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                  struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && to_signed(SEM_ADD(x, y, msk), msk) == nw.s.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && to_signed(SEM_ADD(x, y, msk), msk) == nw.s.min);

*/

void eval_add(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk);

#endif
