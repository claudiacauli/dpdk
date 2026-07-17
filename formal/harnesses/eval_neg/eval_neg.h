#ifndef EVAL_NEG_H
#define EVAL_NEG_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*
 * BPF_NEG negates the register's w-bit pattern (BPF_NEG_ALU in
 * lib/bpf/bpf_exec.c does `-x` on uint32_t/uint64_t), so the result
 * pattern is (-x) mod 2^w — written LINEARLY below as neg_pat, avoiding
 * bitwise operators in the spec altogether. There is no source operand.
 *
 * WITNESS SET: a register abstracts the value set satisfying BOTH
 * tracks — pattern within the unsigned range AND canonical
 * (sign-extended) reading within the signed range. For the independent
 * per-track operators either constraint alone gives a (stronger, still
 * provable) statement, but eval_neg EXCHANGES information across tracks
 * (cross_limits clamps u from s and s from u), so its result is sound
 * only for values in the intersection — a u-witness whose reading lies
 * outside the s-range (e.g. pattern 0x80000000 against s = [-1, 0]) is
 * a value the register can never hold, and quantifying over it makes
 * even a correct implementation falsifiable. Both predicates therefore
 * constrain the witness by both input tracks.
 */
/*@
logic integer neg_pat(integer x, integer msk) =
	x == 0 ? 0 : msk + 1 - x;

predicate eval_neg_unsigned_soundness(struct bpf_reg_val od,
                                       struct bpf_reg_val nw,
                                       uint64_t msk) =
	\forall integer x;
		od.u.min <= x <= od.u.max &&
		od.s.min <= to_signed(x, msk) <= od.s.max
			==> nw.u.min <= neg_pat(x, msk) <= nw.u.max;

predicate eval_neg_signed_soundness(struct bpf_reg_val od,
                                     struct bpf_reg_val nw,
                                     uint64_t msk) =
	\forall integer x;
		od.u.min <= x <= od.u.max &&
		od.s.min <= to_signed(x, msk) <= od.s.max
			==> nw.s.min <= to_signed(neg_pat(x, msk), msk)
			    <= nw.s.max;
*/

void eval_neg(struct bpf_reg_val *rd, size_t opsz, uint64_t msk);

#endif /* EVAL_NEG_H */
