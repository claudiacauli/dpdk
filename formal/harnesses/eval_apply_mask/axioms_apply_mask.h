#ifndef AXIOMS_APPLY_MASK_H
#define AXIOMS_APPLY_MASK_H

/*
 * TU-scoped block algebra for the 32-bit op mask: facts about the
 * block (x & ~m) / low (x & m) decomposition that WP's Cbits cannot
 * fold (same limitation as the land_* family in common/axioms.h).
 * FIX_APPLY_MASK_OPT's keep branch stores masked values and its
 * straddle branch tops out, so uord/usound/uopt need: the decomposition
 * (split), block monotonicity and the full 2^32 gap between distinct
 * blocks (mono/gap), same-block ranges keeping the block and ordering
 * the lows (block_range), a block being low-clean (blockzero), and the
 * value just below a block boundary having all-ones lows (predtop).
 *
 * All six are trusted axioms in the land_* tradition: CBMC-validated in
 * axiom_validation/validate_specs_axioms.c (cells + vacuity probes) and
 * brute-checked over 300M uint64 samples incl. both corners
 * (scratchpad brute_block_axioms.c, 2026-07-21). For the 64-bit op
 * mask ~mask == 0: every straddle condition is false and the facts are
 * trivial, so only the 32-bit constants are axiomatized. TU-scoped on
 * purpose -- keep them out of other harnesses' e-matching space.
 */
/*@
axiomatic ApplyMaskBlocks {
	axiom land_split_u32:
		\forall integer x;
		0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
		x == (x & 0xFFFFFFFF00000000) + (x & 0xFFFFFFFF);

	axiom land_block_mono_u32:
		\forall integer x, y;
		0 <= x <= y <= 0xFFFFFFFFFFFFFFFF ==>
		(x & 0xFFFFFFFF00000000) <= (y & 0xFFFFFFFF00000000);

	axiom land_block_gap_u32:
		\forall integer x, y;
		(x & 0xFFFFFFFF00000000) < (y & 0xFFFFFFFF00000000) ==>
		(x & 0xFFFFFFFF00000000) + 0x100000000 <= (y & 0xFFFFFFFF00000000);

	axiom land_block_range_u32:
		\forall integer x, y, z;
		0 <= x && y <= 0xFFFFFFFFFFFFFFFF && x <= z <= y &&
		(x & 0xFFFFFFFF00000000) == (y & 0xFFFFFFFF00000000) ==>
		((z & 0xFFFFFFFF00000000) == (x & 0xFFFFFFFF00000000) &&
		 (x & 0xFFFFFFFF) <= (z & 0xFFFFFFFF) <= (y & 0xFFFFFFFF));

	axiom land_blockzero_u32:
		\forall integer x;
		((x & 0xFFFFFFFF00000000) & 0xFFFFFFFF) == 0;

	axiom block32_predtop:
		\forall integer x;
		0x100000000 <= (x & 0xFFFFFFFF00000000) ==>
		(((x & 0xFFFFFFFF00000000) - 1) & 0xFFFFFFFF) == 0xFFFFFFFF;

	// Bridge: the block is the shifted Euclidean quotient. Lets the
	// CONTRACT state block equality in div terms (x / 0x100000000) --
	// built-in arithmetic that seeds no custom e-matching in consumer
	// TUs -- while the BODY branches on the & ~mask form (2026-07-28:
	// the & ~mask contract terms were tipping eval_alu cliff stones).
	axiom land_block_div_u32:
		\forall integer x;
		0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
		(x & 0xFFFFFFFF00000000) == 0x100000000 * (x / 0x100000000);
}
*/

#endif /* AXIOMS_APPLY_MASK_H */
