#ifndef LEMMAS_CANON_H
#define LEMMAS_CANON_H

#include "specs.h"

/*
 * Canonical pattern/value round-trip, split out of common/axioms_shift_opt.h
 * so that a TU needing only THIS fact does not also import that header's two
 * quantified branch-selection axioms.
 *
 * WHY THE SPLIT EXISTS (measured, do not re-merge). eval_arsh needs the
 * round-trip but uses NEITHER axiom -- it has no RTE_LEN2MASK guard, so
 * len2mask_shift_u is dead there, and its signed track has no widening branch,
 * so lsr_sign_clear is dead too. Importing them anyway cost real proof
 * capacity: eval_arsh's usound went from 96/97 in 30m (HEAD) to 93/97 in 60m
 * with the full header included -- three NEW timing-out split parts (04, 84,
 * 88) on top of the pre-existing part02. Quantified axioms perturb every PO in
 * their translation unit whether or not any goal uses them, which is exactly
 * what axioms_shift_opt.h's own header comment warns about.
 *
 * This file contains NO axioms and adds no trust burden: the single lemma is
 * discharged by WP (CVC5, ~80ms). It is validated in
 * axiom_validation/validate_specs_axioms.c (shift_opt_family) as well, purely
 * as a guard against a later restatement quietly turning it into an axiom.
 */

/*@
// Encoding a canonical signed value as its w-bit pattern and decoding again is
// the identity. Op-optimality witnesses are PATTERNS (`((uint64_t)s.max) & msk`)
// while the _sum_ stones and the shift_id identities speak of CANONICAL values,
// so every signed optimality chain crosses between the two representations
// exactly here.
//
// eval_rsh and eval_lsh get this for free -- their sopt guards force s.min >= 0,
// where the encoding is the identity outright. eval_arsh is sign-aware and
// admits negative endpoints, so it needs the real wrapping round-trip. Compare
// to_signed_pattern_id in axioms_and.h, which is the same fact for the
// unwrapped `w & m` term shape and is TU-scoped to eval_and.
lemma to_signed_canon_rt:
	\forall integer w, m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	-(m >> 1) - 1 <= w <= (m >> 1)
	==> to_signed(((uint64_t)w) & m, m) == w;
*/

#endif /* LEMMAS_CANON_H */
