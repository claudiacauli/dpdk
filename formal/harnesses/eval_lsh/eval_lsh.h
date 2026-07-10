#ifndef EVAL_LSH_H
#define EVAL_LSH_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
// Soundness quantifies shift amounts y only over [0, op_bits(msk)):
// for y >= op_bits the implementation widens to full width
// (eval_max_bound), so any machine semantics for oversized shifts is
// covered by ufull/sfull-style bounds regardless.
predicate eval_lsh_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                      struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max &&
		y < op_bits(msk)
			==> nw.u.min <= ((x << y) & msk) <= nw.u.max;

// Signed result of a w-bit left shift: shift the w-bit pattern of the
// canonical value v ((uint64_t)v & msk, non-negative so & has axiom
// support), mask back to w bits, sign-extend.
predicate eval_lsh_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		od.s.min <= v <= od.s.max && os.u.min <= y <= os.u.max &&
		y < op_bits(msk)
			==> nw.s.min <=
				to_signed(((((uint64_t)v) & msk) << y) & msk, msk)
				<= nw.s.max;
*/

void eval_lsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
