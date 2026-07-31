#ifndef EVAL_DIVMOD_H
#define EVAL_DIVMOD_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
predicate eval_divmod_unsigned_soundness(integer op, struct bpf_reg_val od,
                                          struct bpf_reg_val os,
                                          struct bpf_reg_val nw,
                                          uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		1 <= y
			==> nw.u.min <= (op == BPF_DIV ? x / y : x % y)
			    <= nw.u.max;

predicate eval_divmod_signed_soundness(integer op, struct bpf_reg_val od,
                                        struct bpf_reg_val os,
                                        struct bpf_reg_val nw,
                                        uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		1 <= y
			==> nw.s.min <=
			    to_signed(op == BPF_DIV ? x / y : x % y, msk)
			    <= nw.s.max;

predicate eval_divmod_unsigned_optimal(integer op, struct bpf_reg_val od,
                                       struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && 1 <= y &&
		(op == BPF_DIV ? x / y : x % y) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && 1 <= y &&
		(op == BPF_DIV ? x / y : x % y) == nw.u.min);

predicate eval_divmod_signed_optimal(integer op, struct bpf_reg_val od,
                                     struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && 1 <= y &&
		to_signed(op == BPF_DIV ? x / y : x % y, msk) == nw.s.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && 1 <= y &&
		to_signed(op == BPF_DIV ? x / y : x % y, msk) == nw.s.min);
*/

const char *eval_divmod(uint32_t op, struct bpf_reg_val *rd,
	struct bpf_reg_val *rs, uint64_t msk);

#endif
