#ifndef EVAL_LSH_H
#define EVAL_LSH_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@
predicate eval_lsh_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                      struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		y < op_bits(msk)
			==> nw.u.min <= ((x << y) & msk) <= nw.u.max;

predicate eval_lsh_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk) &&
		y < op_bits(msk)
			==> nw.s.min <=
				to_signed(((((uint64_t)v) & msk) << y) & msk, msk)
				<= nw.s.max;

predicate eval_lsh_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && y < op_bits(msk) && ((x << y) & msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && y < op_bits(msk) && ((x << y) & msk) == nw.u.min);

predicate eval_lsh_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                  struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer v, y; bin_witness(od, os, v, y, msk) && y < op_bits(msk) &&
		to_signed(((((uint64_t)v) & msk) << y) & msk, msk) == nw.s.max) &&
	(\exists integer v, y; bin_witness(od, os, v, y, msk) && y < op_bits(msk) &&
		to_signed(((((uint64_t)v) & msk) << y) & msk, msk) == nw.s.min);
*/

void eval_lsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
