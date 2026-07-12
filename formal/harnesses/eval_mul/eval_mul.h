#ifndef EVAL_MUL_H
#define EVAL_MUL_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_mul_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, w;
		od.s.min <= v <= od.s.max && os.s.min <= w <= os.s.max
			==> nw.s.min <= to_signed((v * w) & msk, msk) <= nw.s.max;

predicate eval_mul_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max
			==> nw.u.min <= ((x * y) & msk) <= nw.u.max;
*/

void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif /* EVAL_MUL_H */
