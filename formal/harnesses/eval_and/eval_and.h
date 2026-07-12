#ifndef EVAL_AND_H
#define EVAL_AND_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_and_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		od.s.min <= v <= od.s.max && os.u.min <= y <= os.u.max
			==> nw.s.min <= to_signed(v & y, msk) <= nw.s.max;

predicate eval_and_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max
			==> nw.u.min <= (x & y) <= nw.u.max;
*/

void eval_and(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_AND_H */
