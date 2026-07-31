#ifndef AXIOMS_APPLY_MASK_H
#define AXIOMS_APPLY_MASK_H

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

	axiom land_block_div_u32:
		\forall integer x;
		0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
		(x & 0xFFFFFFFF00000000) == 0x100000000 * (x / 0x100000000);
}
*/

#endif
