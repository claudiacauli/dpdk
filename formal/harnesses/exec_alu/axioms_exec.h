#ifndef AXIOMS_EXEC_H
#define AXIOMS_EXEC_H

/*
 * Trusted axioms for the EXECUTOR-AGREEMENT proofs, TU-scoped like the
 * other axioms_*.h headers (include from exec_*.c only). Same trust
 * contract: validated in axiom_validation/validate_specs_axioms.c
 * (land_mod_family), and mathematically these are the definition of
 * "low w bits": for x >= 0, x & (2^w - 1) == x mod 2^w.
 *
 * WHY THE EXEC PROOFS NEED THEM WHEN THE eval_* PROOFS NEVER DID: the
 * validator corpus always reasons about values already WITHIN width
 * (range_within_width is a precondition everywhere), so the land_id /
 * land_wrap axioms' bounded domains sufficed. The executor's machine
 * arithmetic is the other way round: operands are arbitrary uint64
 * register contents that the case-arm CASTS truncate — to_uint32(x)
 * for any x, to_uint64 of a shift product up to 2^127 — and WP encodes
 * those casts as mod-2^w arithmetic. These two facts let the masked
 * SEM_* forms meet the cast forms at mod arithmetic, where the
 * provers' built-in Euclidean theory does the rest (the div-form
 * contract trick from eval_apply_mask, axioms_apply_mask.h).
 */
/*@
axiomatic LandMod {
	axiom land_u32_mod:
		\forall integer x;
		0 <= x ==> (x & 0xFFFFFFFF) == x % 0x100000000;
	axiom land_u64_mod:
		\forall integer x;
		0 <= x ==> (x & 0xFFFFFFFFFFFFFFFF) == x % 0x10000000000000000;
	// The cast-side twins: WP's to_uintN is axiomatized by identity-
	// on-range plus a +/-2^N wrap recursion, which cannot unwrap the
	// executor's large intermediates (a 64-bit lsl product reaches
	// 2^127 — the shl32_ext_id wall, axioms_arsh.h). Supply the
	// closed-form identity whole; for non-negative mathematical
	// integers these ARE the C cast semantics.
	axiom cast_u32_mod:
		\forall integer x;
		0 <= x ==> ((uint32_t)x) == x % 0x100000000;
	axiom cast_u64_mod:
		\forall integer x;
		0 <= x ==> ((uint64_t)x) == x % 0x10000000000000000;
	// Two's-complement NEGATION at 32 bits. Needed by the 32-bit NEG arm
	// ALONE: BPF_NEG_ALU negates the UNCAST uint64 register and only then
	// truncates, so after Qed collapses the double cast the goal is
	//     neg_pat(land(0xFFFFFFFF, x), 0xFFFFFFFF) = to_uint32(-x)
	// i.e. to_uint32 applied to a NEGATIVE argument — the one place in
	// the ALU where the mod bridges above cannot fire (they need
	// 0 <= x). Every other 32-bit arm truncates its operands first.
	// Stated with `land` (not `%`) so it matches the goal's e-node
	// directly; conclusion is the neg_pat case split written out, which
	// is definitional for two's-complement negation. Validated in
	// validate_specs_axioms.c (land_mod_family).
	axiom cast_u32_neg:
		\forall integer x;
		0 <= x ==>
		((uint32_t)(-x)) ==
		    ((x & 0xFFFFFFFF) == 0 ? 0 : 0x100000000 - (x & 0xFFFFFFFF));
}
*/

#endif /* AXIOMS_EXEC_H */
