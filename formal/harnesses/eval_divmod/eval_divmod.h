#ifndef EVAL_DIVMOD_H
#define EVAL_DIVMOD_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*
 * BPF_DIV / BPF_MOD are UNSIGNED operations on the register's w-bit
 * pattern, so BOTH soundness predicates quantify their witnesses over the
 * operands' unsigned ranges; the signed track merely claims to bound the
 * canonical (sign-extended) value of the result pattern. A zero divisor
 * never produces a destination value: the interpreter aborts the program
 * (BPF_DIV_ZERO_CHECK in lib/bpf/bpf_exec.c) and constant-zero divisors
 * are rejected by the validator itself ("division by 0"), so the
 * predicates range over divisor witnesses y >= 1 only. Results never
 * exceed the dividend (x/y <= x, x%y <= x), so no masking is involved.
 */
/*@
predicate eval_divmod_unsigned_soundness(integer op, struct bpf_reg_val od,
                                          struct bpf_reg_val os,
                                          struct bpf_reg_val nw,
                                          uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max &&
		1 <= y
			==> nw.u.min <= (op == BPF_DIV ? x / y : x % y)
			    <= nw.u.max;

predicate eval_divmod_signed_soundness(integer op, struct bpf_reg_val od,
                                        struct bpf_reg_val os,
                                        struct bpf_reg_val nw,
                                        uint64_t msk) =
	\forall integer x, y;
		od.u.min <= x <= od.u.max && os.u.min <= y <= os.u.max &&
		1 <= y
			==> nw.s.min <=
			    to_signed(op == BPF_DIV ? x / y : x % y, msk)
			    <= nw.s.max;
*/

const char *eval_divmod(uint32_t op, struct bpf_reg_val *rd,
	struct bpf_reg_val *rs, uint64_t msk);

#endif /* EVAL_DIVMOD_H */
