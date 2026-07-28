#ifndef EVAL_NEG_H
#define EVAL_NEG_H

#include "../../common/shared.h"
#include "../../common/specs.h"
#include "../../common/semantics.h"

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
// neg_pat MOVED to common/semantics.h (2026-07-28), together with its
// "do NOT state involution lemmas" rationale (measured: 4.8s -> 5m07s
// timeout): it is part of the CONCRETE SEMANTICS of negation, so the
// executor-agreement harness cites the same symbol. Image terms below
// are SEM_NEG, whose expansion is the identical AST. The GROUND stones
// in eval_neg.c (uopt_inv_*, sopt_inv_*) remain the way the involution
// is supplied.

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

// OP-OPTIMALITY (here: neg-optimal). Soundness says the computed range
// CONTAINS the image; op-optimality says it is the SMALLEST interval that
// does — each endpoint is ATTAINED by a real value the register can hold,
// i.e. an un_witness: a pattern in the unsigned range whose signed reading is
// also in the signed range (Marat's intersection semantics). Since the
// intersection witness set is a subset of each single-track set, this
// (intersection) op-optimality implies the weaker per-track version.
// In Abstract Interpretation terms this is the BEST ABSTRACT TRANSFORMER
// condition out = alpha(neg(gamma(in))) restricted to this input.
//
// PRELIMINARY (see optimality_notes.md). BMC-established that eval_neg attains
// all four endpoints when (a) the FIX_NEG_ZERO precision fix is on, (b) the
// INPUT is SELF-OPTIMAL (its own range endpoints are attained — self_optimal()
// in specs.h), and (c) the signed range is not floored at the width-min
// INT_MIN (the lone residual: the wrap case widens s.max). Not yet WP-proved;
// the witness for each endpoint is the unique neg_pat preimage of that endpoint.
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

#endif /* EVAL_NEG_H */
