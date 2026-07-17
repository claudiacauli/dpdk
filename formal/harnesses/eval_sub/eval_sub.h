#ifndef EVAL_SUB_H
#define EVAL_SUB_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
// Machine result of a w-bit subtraction, for differences within one wrap
// (|d| <= msk, guaranteed by the operand ranges below): piecewise-linear
// on purpose — a negative d under ACSL's `&` has no usable axioms, while
// this form needs none (same strategy as to_signed for eval_add).
logic integer wrap_diff(integer d, integer msk) =
      d >= 0 ? d : d + (msk + 1);

predicate eval_sub_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= wrap_diff(x - y, msk) <= nw.u.max;

// to_signed comes from common/specs.h

predicate eval_sub_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.s.min <= to_signed(wrap_diff(x - y, msk), msk) <= nw.s.max;

*/

void eval_sub(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk);

#endif
