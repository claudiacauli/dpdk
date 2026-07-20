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

// neg_pat maps [0,msk] onto itself and is an INVOLUTION there. That is what
// makes op-optimality provable for eval_neg at all: the witness for an output
// endpoint e is not something to be searched for, it is FORCED to be neg_pat(e).
//
// DELIBERATELY NOT STATED AS LEMMAS HERE -- do not add them back. Quantified
// lemmas of the form
//     \forall x, m; 0 <= x <= m ==> neg_pat(neg_pat(x, m), m) == x
// were tried and MEASURED: they take eval_neg's usound from 1/1 in 4.8s to a
// TIMEOUT at 5m07s. The reason is that usound itself quantifies over neg_pat, so
// such a lemma's trigger fires all over its proof obligation.
//
// They are also unnecessary. neg_pat is a DEFINED logic function (not
// axiomatised), so WP unfolds it directly: the four GROUND instances stated as
// stones in eval_neg.c (uopt_inv_*, sopt_inv_*) each prove 1/1 on their own, and
// uopt/sopt prove 1024/1024 with no lemma in scope at all.
//
// General rule this instance illustrates: when a fact is only needed at
// specific terms, state it as a GROUND STONE, not a quantified lemma. A lemma is
// a hypothesis in every PO of the translation unit and can wreck a neighbouring
// cliff goal.

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
	(\exists integer x; un_witness(od, x, msk) && neg_pat(x, msk) == nw.u.max) &&
	(\exists integer x; un_witness(od, x, msk) && neg_pat(x, msk) == nw.u.min);

predicate eval_neg_signed_optimal(struct bpf_reg_val od,
                                  struct bpf_reg_val nw,
                                  uint64_t msk) =
	(\exists integer x; un_witness(od, x, msk) &&
		to_signed(neg_pat(x, msk), msk) == nw.s.max) &&
	(\exists integer x; un_witness(od, x, msk) &&
		to_signed(neg_pat(x, msk), msk) == nw.s.min);
*/

void eval_neg(struct bpf_reg_val *rd, size_t opsz, uint64_t msk);

#endif /* EVAL_NEG_H */
