#ifndef EVAL_ARSH_H
#define EVAL_ARSH_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "axioms_arsh.h"

/*@
// Arithmetic right shift. ACSL's >> on mathematical integers IS floor
// division by 2^y, i.e. exactly the arithmetic shift the machine
// performs on the sign-extended value — so the signed predicate needs
// no masking at all: canonical values stay canonical under v >> y.
predicate eval_arsh_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, y;
		bin_witness(od, os, v, y, msk) &&
		y < op_bits(msk)
			==> nw.s.min <= (to_signed(v, msk) >> y) <= nw.s.max;

// Unsigned view of the same operation: take the pattern x, sign-extend
// (to_signed), arithmetic-shift, re-encode as a w-bit pattern.
predicate eval_arsh_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk) &&
		y < op_bits(msk)
			==> nw.u.min <=
				(((uint64_t)(to_signed(x, msk) >> y)) & msk)
				<= nw.u.max;
*/

void eval_arsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
