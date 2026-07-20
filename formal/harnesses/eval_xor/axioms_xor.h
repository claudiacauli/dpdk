#ifndef AXIOMS_XOR_H
#define AXIOMS_XOR_H

/* specs.h (via axioms.h) provides the shared logic surface (to_signed);
 * kept for parity with axioms_and.h / axioms_or.h. */
#include "../../common/specs.h"

/*
 * Trusted axioms used ONLY by the eval_xor proof, TU-scoped like
 * common/axioms_and.h / axioms_or.h / axioms_clz.h: quantified axioms
 * perturb the SMT search of every PO in whose translation unit they
 * appear, so keep them out of the shared header and include from
 * eval_xor.c only. Same trust contract as axioms.h: every axiom is
 * CBMC-proved over its full domain in
 * axiom_validation/validate_specs_axioms.c.
 *
 * WP's Cbits theory has no bounds/extensionality axioms for bitwise XOR
 * (the twin of the land and lor gaps). eval_xor over-approximates the XOR
 * by the OR estimate eval_uor_max, so the workhorse is lxor_le_lor
 * (a^b <= a|b): chained with eval_uor_max uor_cover ensures it bounds
 * every XOR witness. The rest mirror the OR family: non-negativity, a
 * mask bound for the constants branch, canonical closure for the signed
 * constants branch, and the symbolic-mask round-trip for ssound.
 */
/*@
axiomatic LxorBounds {
	// XOR of two non-negative values is non-negative (carries the
	// unsigned/signed soundness lower bounds, where the non-const
	// branches set the new min to 0).
	axiom lxor_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a ^ b);
	// XOR sets no bit that OR does not: a^b <= a|b. THE cover workhorse —
	// composed with eval_uor_max's uor_cover ((a|b) <= result) it bounds
	// every XOR witness by the tracked OR estimate.
	axiom lxor_le_lor:
		\forall integer a, b; 0 <= a && 0 <= b ==> (a ^ b) <= (a | b);
	// Two values under one all-ones mask XOR to a value still under it
	// (XOR sets no bit outside the shared window). Mask-concrete for the
	// two full masks so it fires without a ground-land shape guard after
	// the opsz split; carries uwidth in the unsigned constants branch
	// (u.max ^= rs.u.max, no eval_uor_max call to lean on there).
	axiom lxor_mask32:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
		==> (a ^ b) <= 0xFFFFFFFF;
	axiom lxor_mask64:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
		==> (a ^ b) <= 0xFFFFFFFFFFFFFFFF;
	// Signed XOR is closed under the canonical w-bit range: two
	// sign-extended w-bit values XOR to a sign-extended w-bit value (bits
	// w-1..63 are all the sign bit on each side, so they are all
	// sign_a ^ sign_b in the result). Twin of lor_canon_32/64; carries
	// eval_xor's signed constants branch (s.max ^= rs.s.max on
	// possibly-negative int64 values) for swidth/sord.
	axiom lxor_canon_32:
		\forall integer a, b;
		-0x80000000 <= a <= 0x7FFFFFFF &&
		-0x80000000 <= b <= 0x7FFFFFFF
		==> -0x80000000 <= (a ^ b) <= 0x7FFFFFFF;
	axiom lxor_canon_64:
		\forall integer a, b;
		-0x8000000000000000 <= a <= 0x7FFFFFFFFFFFFFFF &&
		-0x8000000000000000 <= b <= 0x7FFFFFFFFFFFFFFF
		==> -0x8000000000000000 <= (a ^ b) <= 0x7FFFFFFFFFFFFFFF;
	// Decode commutes with XOR-by-a-pattern (the XOR twin of
	// to_signed_lor_pat in axioms_or.h): for canonical v and a w-bit
	// pattern p, decoding the masked XOR of the two patterns equals
	// XORing v with p's decoded value. The mask stays SYMBOLIC (pinned to
	// one of the two masks by the disjunction every PO carries) so the
	// trigger matches eval_xor's ssound term to_signed((v ^ y) & msk, msk)
	// with its symbolic msk, and needs no opsz case split to resolve an
	// ite. Proof: (v^p)&m == (v ^ to_signed(p,m)) & m, and v^to_signed(p,m)
	// is canonical (lxor_canon), so to_signed round-trips it.
	axiom to_signed_lxor_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed((v ^ p) & m, m) == (v ^ to_signed(p, m));
	// Decode commutes with XOR of TWO patterns (the both-pattern form of
	// to_signed_lxor_pat above). Needed by ssound's signed-CONSTANT
	// branch (split parts 01/08/15 = the sw_xor_c path x each u-path):
	// there the bin_witness decode is pinned to a possibly NEGATIVE
	// constant whose pattern exceeds msk >> 1 — outside the canonical
	// window, so to_signed_lxor_pat never fires (lxor is not
	// AC-normalized, the second slot cannot rescue it) and nothing
	// matches to_signed((v ^ y) & msk, msk). Sign-extension replicates
	// bit w-1 into bits w..63 and XOR is bitwise, so XOR of
	// sign-extensions == sign-extension of the masked XOR. Mask kept
	// SYMBOLIC as above. Isolated experiment (2026-07-20): the s-const
	// obligation times out with the axiom set above, proves in 36ms with
	// this one added.
	axiom to_signed_lxor_both:
		\forall integer p, q, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= p <= m && 0 <= q <= m
		==> to_signed((p ^ q) & m, m)
			== (to_signed(p, m) ^ to_signed(q, m));
}
*/

#endif /* AXIOMS_XOR_H */
