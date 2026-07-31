#ifndef EVAL_NEG_H
#define EVAL_NEG_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "../../common/semantics.h"

/*@

predicate eval_neg_unsigned_soundness(struct bpf_reg_val od,
                                       struct bpf_reg_val nw,
                                       uint64_t msk) =
	\forall integer x;
		od.u.min <= x <= od.u.max &&
		od.s.min <= to_signed(x, msk) <= od.s.max
			==> nw.u.min <= SEM_NEG(x, msk) <= nw.u.max;

predicate eval_neg_signed_soundness(struct bpf_reg_val od,
                                     struct bpf_reg_val nw,
                                     uint64_t msk) =
	\forall integer x;
		od.u.min <= x <= od.u.max &&
		od.s.min <= to_signed(x, msk) <= od.s.max
			==> nw.s.min <= to_signed(SEM_NEG(x, msk), msk)
			    <= nw.s.max;

predicate eval_neg_unsigned_optimal(struct bpf_reg_val od,
                                    struct bpf_reg_val nw,
                                    uint64_t msk) =
	(\exists integer x; un_witness(od, x, msk) && SEM_NEG(x, msk) == nw.u.max) &&
	(\exists integer x; un_witness(od, x, msk) && SEM_NEG(x, msk) == nw.u.min);

predicate eval_neg_signed_optimal(struct bpf_reg_val od,
                                  struct bpf_reg_val nw,
                                  uint64_t msk) =
	(\exists integer x; un_witness(od, x, msk) &&
		to_signed(SEM_NEG(x, msk), msk) == nw.s.max) &&
	(\exists integer x; un_witness(od, x, msk) &&
		to_signed(SEM_NEG(x, msk), msk) == nw.s.min);
*/

void eval_neg(struct bpf_reg_val *rd, size_t opsz, uint64_t msk);

#endif
