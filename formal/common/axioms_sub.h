#ifndef AXIOMS_SUB_H
#define AXIOMS_SUB_H

#include "axioms.h"

/*@
axiomatic LandWrapNeg {
	axiom land_wrapneg_u32:
		\forall integer x; -0x100000000 <= x < 0 ==> (x & 0xFFFFFFFF) == x + 0x100000000;
	axiom land_wrapneg_u64:
		\forall integer x;
		-0x10000000000000000 <= x < 0 ==> (x & 0xFFFFFFFFFFFFFFFF) == x + 0x10000000000000000;
}
*/

#endif
