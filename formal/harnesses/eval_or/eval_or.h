#ifndef EVAL_OR_H
#define EVAL_OR_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_or_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk)
			==> nw.s.min <= to_signed((v | y) & msk, msk) <= nw.s.max;

predicate eval_or_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= (x | y) <= nw.u.max;
*/

void eval_or(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_OR_H */
