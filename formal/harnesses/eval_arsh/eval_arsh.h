#ifndef EVAL_ARSH_H
#define EVAL_ARSH_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "axioms_arsh.h"
#include "../../common/lemmas_canon.h"

/*@
predicate eval_arsh_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk) &&
		y < op_bits(msk)
			==> nw.s.min <= (to_signed(v, msk) >> y) <= nw.s.max;

predicate eval_arsh_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		y < op_bits(msk)
			==> nw.u.min <=
				(((uint64_t)(to_signed(x, msk) >> y)) & msk)
				<= nw.u.max;

predicate eval_arsh_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                   struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer v, y; bin_witness(od, os, v, y, msk) && y < op_bits(msk) && (to_signed(v, msk) >> y) == nw.s.max) &&
	(\exists integer v, y; bin_witness(od, os, v, y, msk) && y < op_bits(msk) && (to_signed(v, msk) >> y) == nw.s.min);

predicate eval_arsh_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && y < op_bits(msk) &&
		(((uint64_t)(to_signed(x, msk) >> y)) & msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && y < op_bits(msk) &&
		(((uint64_t)(to_signed(x, msk) >> y)) & msk) == nw.u.min);
*/

void eval_arsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
