#ifndef AXIOMS_OR_H
#define AXIOMS_OR_H

/* specs.h (via axioms.h) provides the shared logic surface; the OR
 * axioms below are self-contained but keep the include for parity with
 * axioms_and.h. */
#include "specs.h"

/*
 * Trusted axioms used ONLY by the eval_uor_max proof (and, later,
 * eval_or / eval_xor), TU-scoped like common/axioms_and.h and
 * common/axioms_clz.h: quantified axioms perturb the SMT search of every
 * PO in whose translation unit they appear, so keep them out of the
 * shared header and include from eval_uor_max.c only. Same trust
 * contract as axioms.h: every axiom is CBMC-proved over its full domain
 * in axiom_validation/validate_specs_axioms.c.
 *
 * WP's Cbits theory has no bounds/extensionality axioms for bitwise OR
 * (the twin of the land_* gap in axioms.h), so none of these are
 * first-order consequences of the shipped model. OR only SETS bits, so
 * the shapes differ from the AND family: a common all-ones cover bounds
 * the result (mask32/64, half32/64), and the union of two all-ones masks
 * bounds the OR of any pair drawn beneath them (allones_mono, the cover
 * workhorse — its all-ones guards are discharged by eval_umax_bits's
 * `shape` ensures, matched symbolically, not by evaluating a ground
 * land).
 */
/*@
axiomatic LorBounds {
	// OR of two non-negative values is non-negative (carries uor_nonneg).
	axiom lor_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a | b);
	// OR only SETS bits, so each non-negative operand is a lower bound on
	// the result (the twin of land_le_mask's upper bound). Carries the
	// range-ordering and lower-bound soundness goals in eval_or, where the
	// new u.min / s.min are RTE_MAX(old mins) and every concrete pair OR's
	// to at least its own operands.
	axiom lor_lb:
		\forall integer a, b;
		0 <= a && 0 <= b ==> a <= (a | b) && b <= (a | b);
	// ORing with zero is the identity: eval_or's usound lower bound needs
	// (x | 0) to fold back to x when a witness has no bits from one side.
	axiom lor_id0:
		\forall integer a; 0 <= a ==> (a | 0) == a && (0 | a) == a;
	// Signed OR is closed under the canonical w-bit range: two
	// sign-extended w-bit values OR to a sign-extended w-bit value (bits
	// w-1..63 are all the sign bit on each side, so they are all sign_a |
	// sign_b in the result). Twin of land_canon_32/64 in axioms_and.h;
	// carries eval_or's signed constants branch (s.max |= rs.s.max on
	// possibly-negative int64 values) for swidth/sord.
	axiom lor_canon_32:
		\forall integer a, b;
		-0x80000000 <= a <= 0x7FFFFFFF &&
		-0x80000000 <= b <= 0x7FFFFFFF
		==> -0x80000000 <= (a | b) <= 0x7FFFFFFF;
	axiom lor_canon_64:
		\forall integer a, b;
		-0x8000000000000000 <= a <= 0x7FFFFFFFFFFFFFFF &&
		-0x8000000000000000 <= b <= 0x7FFFFFFFFFFFFFFF
		==> -0x8000000000000000 <= (a | b) <= 0x7FFFFFFFFFFFFFFF;
	// AND distributes over OR: (a | (b & m)) & m == (a | b) & m. Used on
	// the unsigned soundness path where a masked-OR witness is rewritten.
	// General bitwise identity, holds for any a, b, m.
	axiom lor_land_distrib:
		\forall integer a, b, m;
		((a | (b & m)) & m) == ((a | b) & m);
	// Decode commutes with OR-by-a-pattern (the OR twin of
	// to_signed_land_pat in axioms_and.h): for canonical v and a w-bit
	// pattern p, decoding the masked OR of the two patterns equals ORing
	// v with p's decoded value. The mask stays SYMBOLIC (pinned to one of
	// the two masks by the disjunction every PO carries) so the trigger
	// matches eval_or's ssound term to_signed((v | y) & msk, msk) with
	// its symbolic msk — a constant-mask form could never fire there, and
	// (unlike a stone) needs no opsz case split to resolve an ite. Proof:
	// (v|p)&m == (v | to_signed(p,m)) & m, and v|to_signed(p,m) is
	// canonical (lor_canon), so to_signed round-trips it.
	axiom to_signed_lor_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed((v | p) & m, m) == (v | to_signed(p, m));
	// The cover workhorse: bits of a live in m1's all-ones window and
	// bits of b in m2's, so bits of a|b live in the union window m1|m2.
	// eval_uor_max instantiates this at m1 = eval_umax_bits(v1),
	// m2 = eval_umax_bits(v2); the all-ones guards match those callees'
	// `shape` ensures. (Twin of land_allones_mono in axioms_and.h.)
	axiom lor_allones_mono:
		\forall integer a, b, m1, m2;
		0 <= a <= m1 && 0 <= b <= m2 &&
		(m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0
		==> (a | b) <= (m1 | m2);
	// Common-cover bounds: two values under one all-ones mask OR to a
	// value still under it (OR sets no bit outside the shared window).
	// Mask-concrete for the two full masks and the two half-masks, so
	// they fire without discharging a ground-land shape guard (the
	// axioms_and.h land_half*_id lesson): after the opsz case split the
	// contract's ite-mask is a literal, and these carry uor_width
	// (full masks) and uor_half32/64 (half-masks).
	axiom lor_mask32:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
		==> (a | b) <= 0xFFFFFFFF;
	axiom lor_mask64:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
		==> (a | b) <= 0xFFFFFFFFFFFFFFFF;
	axiom lor_half32:
		\forall integer a, b;
		0 <= a <= 0x7FFFFFFF && 0 <= b <= 0x7FFFFFFF
		==> (a | b) <= 0x7FFFFFFF;
	axiom lor_half64:
		\forall integer a, b;
		0 <= a <= 0x7FFFFFFFFFFFFFFF && 0 <= b <= 0x7FFFFFFFFFFFFFFF
		==> (a | b) <= 0x7FFFFFFFFFFFFFFF;
}
*/

#endif /* AXIOMS_OR_H */
