#ifndef AXIOMS_SHIFT_OPT_H
#define AXIOMS_SHIFT_OPT_H

#include "specs.h"

/*
 * BRANCH-SELECTION facts for the shift family's OP-OPTIMALITY proofs
 * (eval_lsh, eval_rsh, eval_arsh). TU-scoped like common/axioms_and.h --
 * quantified axioms perturb every PO in whose translation unit they
 * appear, so include only from the shift harnesses.
 *
 * WHY THESE EXIST. Soundness never needs them: it holds on BOTH sides of
 * each widening branch. Op-optimality holds only in the NO-WIDEN regime,
 * so its proof must show "the ensures guard implies the widening branch
 * was not taken". In every shift operator that obligation reduces to a
 * shift identity with a SYMBOLIC amount, which is exactly what WP's SMT
 * encoding cannot do (the same wall the LenShift family in axioms.h was
 * built for). Each fact is stated in the EXACT term shape the branch
 * condition emits -- RTE_LEN2MASK expands to `lsr(allones, 64 - n)`, so
 * the conclusions are written `64 - (op_bits(m) - q)` and NOT the
 * arithmetically equal `64 - op_bits(m) + q`; a normalised form never
 * matches the goal's e-node and the axiom can never fire.
 *
 * Trust contract, identical to axioms.h: every `axiom` below is validated
 * over its full instantiation domain by
 *
 *     cd axiom_validation && esbmc validate_specs_axioms.c --no-library
 *
 * (function shift_opt_family). ESBMC, not CBMC -- see README: these are
 * bitwise/wrap facts, and CBMC's SAT bit-blasting does not terminate on
 * the 64-bit checks in that file.
 *
 * The two `lemma`s at the bottom are discharged by WP itself and are NOT
 * trusted; they are validated in shift_opt_family as well, purely as a
 * guard against a later restatement quietly turning one into an axiom.
 */

/*@
axiomatic ShiftOptBranchSel {
	// Sign bit of a non-negative in-range signed value is clear.
	// Selects the non-widening branch of eval_rsh's and eval_lsh's
	// signed guard `(uint64_t)s.min >> (opsz - 1) != 0`.
	//
	// This is the CONVERSE of axioms.h's lsr_sign_any (which reads the
	// implication the other way, sign-bit-clear ==> non-negative);
	// soundness only ever needed that direction, optimality needs this
	// one. The shift amount is kept SYMBOLIC as `op_bits(m) - 1` for the
	// reason lsr_sign_any documents: with a constant amount Qed rewrites
	// `(x >> 31) == 0` into a land bitmask test that no longer matches
	// the goal's lsr term. The upper bound is written `m >> 1` because
	// that is the shape signed_range_within_width supplies.
	axiom lsr_sign_clear:
		\forall int64_t v; \forall integer m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= v <= (m >> 1)
		==> (((uint64_t)v) >> (op_bits(m) - 1)) == 0;

	// RTE_LEN2MASK(opsz - q, uint64_t) == msk >> q.
	// Selects the non-widening branch of eval_lsh's unsigned overflow
	// guard `rd->u.max > RTE_LEN2MASK(opsz - rs->u.max, uint64_t)`,
	// against the ensures guard `rd->u.max <= (msk >> rs->u.max)`.
	// For the 64-bit mask the two sides are syntactically identical and
	// the fact is trivial; the 32-bit mask is the one that needs it.
	axiom len2mask_shift_u:
		\forall integer m, q;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= q < op_bits(m)
		==> (0xFFFFFFFFFFFFFFFF >> (64 - (op_bits(m) - q))) == (m >> q);
}
*/

/*@
// RTE_LEN2MASK(opsz - q - 1, int64_t) == (msk >> 1) >> q, the signed twin
// of len2mask_shift_u: it selects the non-widening branch of eval_lsh's
// signed overflow guard. NOT an axiom -- WP discharges it (Alt-Ergo,
// ~30ms), so it carries no trust burden. Kept here rather than in
// axioms.h so the whole branch-selection story reads in one place.
lemma len2mask_shift_s:
	\forall integer m, q;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	0 <= q <= op_bits(m) - 2
	==> (0xFFFFFFFFFFFFFFFF >> (64 - (op_bits(m) - q - 1))) == ((m >> 1) >> q);
*/

/*
 * The canonical round-trip lemma to_signed_canon_rt USED TO LIVE HERE. It now
 * sits in common/lemmas_canon.h -- do not merge it back.
 *
 * eval_arsh needs that lemma but NEITHER axiom above: it has no RTE_LEN2MASK
 * guard (len2mask_shift_u is dead there) and its signed track has no widening
 * branch (lsr_sign_clear is dead too). Importing the axioms anyway measurably
 * cost proof capacity -- eval_arsh's usound went 96/97 in 30m (HEAD) to 93/97
 * in 60m, three NEW timing-out split parts. Include whichever header a harness
 * actually needs, and nothing more.
 *
 * Known and deliberate loose end: by that same rule eval_rsh over-imports too
 * -- it needs lsr_sign_clear only, not the two len2mask_* facts (rsh has no
 * unsigned widening branch and so no RTE_LEN2MASK guard). It is left as-is
 * because it shows NO measured cost: rsh's usound proves in 1m20s and ssound in
 * 51s against a 600s timeout, i.e. with two orders of magnitude of margin.
 * Splitting this header a third time would buy nothing and cost clarity. If rsh
 * ever starts flickering, that is the first thing to try.
 */

#endif /* AXIOMS_SHIFT_OPT_H */
