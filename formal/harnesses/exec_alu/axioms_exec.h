#ifndef AXIOMS_EXEC_H
#define AXIOMS_EXEC_H

/*@
axiomatic LandMod {
	axiom land_u32_mod:
		\forall integer x;
		0 <= x ==> (x & 0xFFFFFFFF) == x % 0x100000000;
	axiom land_u64_mod:
		\forall integer x;
		0 <= x ==> (x & 0xFFFFFFFFFFFFFFFF) == x % 0x10000000000000000;
	axiom cast_u32_mod:
		\forall integer x;
		0 <= x ==> ((uint32_t)x) == x % 0x100000000;
	axiom cast_u64_mod:
		\forall integer x;
		0 <= x ==> ((uint64_t)x) == x % 0x10000000000000000;
	axiom cast_u32_neg:
		\forall integer x;
		0 <= x ==>
		((uint32_t)(-x)) ==
		    ((x & 0xFFFFFFFF) == 0 ? 0 : 0x100000000 - (x & 0xFFFFFFFF));
}
*/

#endif
