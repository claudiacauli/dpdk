#ifndef EVAL_RSH_H
#define EVAL_RSH_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
// Logical right shift; y quantified over [0, op_bits(msk)) — oversized
// shifts are widened to full range by the implementation. On the
// unsigned track no masking is even needed: x <= msk stays <= msk.
predicate eval_rsh_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                      struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		y < op_bits(msk)
			==> nw.u.min <= (x >> y) <= nw.u.max;

// Signed value after a LOGICAL right shift of the w-bit pattern of the
// canonical value v.
predicate eval_rsh_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk) &&
		y < op_bits(msk)
			==> nw.s.min <=
				to_signed((((uint64_t)v) & msk) >> y, msk)
				<= nw.s.max;
*/

void eval_rsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
