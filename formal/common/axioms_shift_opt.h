#ifndef AXIOMS_SHIFT_OPT_H
#define AXIOMS_SHIFT_OPT_H

#include "specs.h"

/*@
axiomatic ShiftOptBranchSel {
	axiom lsr_sign_clear:
		\forall int64_t v; \forall integer m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= v <= (m >> 1)
		==> (((uint64_t)v) >> (op_bits(m) - 1)) == 0;

	axiom len2mask_shift_u:
		\forall integer m, q;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= q < op_bits(m)
		==> (0xFFFFFFFFFFFFFFFF >> (64 - (op_bits(m) - q))) == (m >> q);
}
*/

/*@
lemma len2mask_shift_s:
	\forall integer m, q;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	0 <= q <= op_bits(m) - 2
	==> (0xFFFFFFFFFFFFFFFF >> (64 - (op_bits(m) - q - 1))) == ((m >> 1) >> q);
*/

#endif
