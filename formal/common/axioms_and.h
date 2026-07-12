#ifndef AXIOMS_AND_H
#define AXIOMS_AND_H

/* specs.h (via axioms.h) provides the to_signed logic function the
 * round-trip axioms below reference. */
#include "specs.h"

/*
 * Trusted axioms used ONLY by the eval_and proof, TU-scoped like
 * common/axioms_arsh.h and common/axioms_clz.h (quantified axioms
 * perturb every PO in whose translation unit they appear). Include
 * from eval_and.c only. Same trust contract as axioms.h: every axiom
 * is CBMC-proved in axiom_validation/validate_specs_axioms.c.
 *
 * The shared land_* family is non-negative-only; eval_and's constants
 * branch ANDs canonical SIGNED values (`rd->s.min &= rs->s.min`), and
 * these state that canonical w-bit values are closed under &: both
 * negative gives a negative result (sign bits AND to ones), any
 * non-negative side bounds the result below its width.
 */
/*@
axiomatic LandCanon {
	axiom land_canon_32:
		\forall integer a, b;
		-0x80000000 <= a <= 0x7FFFFFFF &&
		-0x80000000 <= b <= 0x7FFFFFFF
		==> -0x80000000 <= (a & b) <= 0x7FFFFFFF;
	axiom land_canon_64:
		\forall integer a, b;
		-0x8000000000000000 <= a <= 0x7FFFFFFFFFFFFFFF &&
		-0x8000000000000000 <= b <= 0x7FFFFFFFFFFFFFFF
		==> -0x8000000000000000 <= (a & b) <= 0x7FFFFFFFFFFFFFFF;
	// Cover machinery for the soundness ensures. Two-sided: bits of a
	// live in m1's window and bits of b in m2's, so bits of a&b live in
	// the intersection window m1&m2 (carries uand_cover's proof).
	axiom land_allones_mono:
		\forall integer a, b, m1, m2;
		0 <= a <= m1 && 0 <= b <= m2 &&
		(m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0
		==> (a & b) <= (m1 & m2);
	// Masking by an all-ones cover is the identity: the shared land_id
	// family only exists for the two FULL masks, but the signed track
	// masks by msk >> 1 (`s.max & (msk >> 1)`), and the cover
	// instantiations need that to be a no-op on in-range values.
	axiom land_allones_id:
		\forall integer x, m;
		0 <= x <= m && (m & (m + 1)) == 0
		==> (x & m) == x;
	// Mask-concrete instances of the same identity for the two
	// half-masks: land_allones_id's shape hypothesis forces the prover
	// to build and evaluate a fresh ground land node, which stalls even
	// in small POs; these fire like the land_id_u32/u64 precedents.
	axiom land_half32_id:
		\forall integer x;
		0 <= x <= 0x7FFFFFFF ==> (x & 0x7FFFFFFF) == x;
	axiom land_half64_id:
		\forall integer x;
		0 <= x <= 0x7FFFFFFFFFFFFFFF
		==> (x & 0x7FFFFFFFFFFFFFFF) == x;
	// Any-sign bound: bits of a & b are a subset of b's bits for ANY a,
	// including negative — the shared land family is nonneg-only, but
	// the soundness quantifier ranges v over od.s, which spans negative
	// values on the one-sided FIX branch.
	axiom land_nonneg_any:
		\forall integer a, b;
		0 <= b ==> 0 <= (a & b) <= b;
	// One-sided absorption: one covered operand suffices to bound the
	// AND, whatever the other side's bits (the FIX_AND_SIGNED_GUARD
	// branch, where the rs side is only bounded by the full width).
	axiom land_allones_absorb:
		\forall integer a, b, m;
		0 <= a <= m && 0 <= b && (m & (m + 1)) == 0
		==> (a & b) <= m;
	// Sext round-trip: encoding a canonical value to its w-bit pattern
	// and decoding again is the identity — the constants branch of the
	// signed track computes `to_signed((v & w) & msk, msk)` against the
	// stored `v & w`.
	axiom to_signed_land_id_32:
		\forall integer u;
		-0x80000000 <= u <= 0x7FFFFFFF
		==> to_signed(u & 0xFFFFFFFF, 0xFFFFFFFF) == u;
	axiom to_signed_land_id_64:
		\forall integer u;
		-0x8000000000000000 <= u <= 0x7FFFFFFFFFFFFFFF
		==> to_signed(u & 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF) == u;
	// Decode commutes with AND-by-a-pattern: for canonical v and a
	// w-bit pattern p, decoding the AND of the patterns equals ANDing
	// v with p's decoded value. The mask stays SYMBOLIC (pinned by the
	// same two-mask disjunction every PO carries) so the trigger
	// matches the goals' to_signed(v & y, msk) terms, where both
	// operands are heap values — a constant-mask form could never fire
	// there (the Qed land-rewrite lesson, again).
	axiom to_signed_land_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed(v & p, m) == (v & to_signed(p, m));
	// Encode/decode round-trip with SYMBOLIC mask (the constant-mask
	// to_signed_land_id_* forms above cannot fire on goal terms whose
	// mask is the symbolic msk): for canonical w, ANDing by the mask
	// yields exactly w's pattern, and decoding recovers w.
	axiom to_signed_pattern_id:
		\forall integer w, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= w <= (m >> 1)
		==> to_signed(w & m, m) == w;
	// Window absorption: if v fits under an all-ones m, bits of y above
	// m's window cannot meet v, so masking y by m first is a no-op —
	// this rewrites (v & y) into a form whose y-side is bounded by
	// msk>>1, unlocking the uand_cover instantiation on the
	// FIX_AND_SIGNED_GUARD path where y itself is only width-bounded.
	axiom land_absorb_window:
		\forall integer v, y, m;
		0 <= v <= m && (m & (m + 1)) == 0 && 0 <= y
		==> (v & y) == (v & (y & m));
}
*/

#endif /* AXIOMS_AND_H */
