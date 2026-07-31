#ifndef AXIOMS_MUL_H
#define AXIOMS_MUL_H

#include "../../common/specs.h"

/*@
axiomatic MulBounds {
	axiom mul_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a * b);
	axiom mul_mono:
		\forall integer a, b, c, d;
		0 <= a <= c && 0 <= b <= d ==> (a * b) <= (c * d);
	axiom mul_bound_u32:
		\forall integer a, b;
		0 <= a <= 0xFFFF && 0 <= b <= 0xFFFF ==> (a * b) <= 0xFFFFFFFF;
	axiom mul_bound_u64:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
		==> (a * b) <= 0xFFFFFFFFFFFFFFFF;
	axiom mul_bound_s32:
		\forall integer a, b;
		0 <= a <= 0x7FFF && 0 <= b <= 0x7FFF ==> (a * b) <= 0x7FFFFFFF;
	axiom mul_bound_s64:
		\forall integer a, b;
		0 <= a <= 0x7FFFFFFF && 0 <= b <= 0x7FFFFFFF
		==> (a * b) <= 0x7FFFFFFFFFFFFFFF;
	axiom mul_mask_wrap:
		\forall integer a, b, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF)
		==> (((uint64_t)((uint64_t)a * (uint64_t)b)) & m) == ((a * b) & m);
#ifdef PROVE_MUL_LEMMAS
	axiom mul_sext_congr:
		\forall integer v, w, c, e, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= v <= m && 0 <= w <= m &&
		to_signed(v, m) == c && to_signed(w, m) == e
		==> to_signed((v * w) & m, m) == to_signed((c * e) & m, m);
#endif
}
*/

/*@
lemma half_mask_u32: (0xFFFFFFFF >> 16) == 0xFFFF;
lemma half_mask_u64: (0xFFFFFFFFFFFFFFFF >> 32) == 0xFFFFFFFF;
lemma half_mask_s32: (0x7FFFFFFF >> 16) == 0x7FFF;
lemma half_mask_s64: (0x7FFFFFFFFFFFFFFF >> 32) == 0x7FFFFFFF;
*/

#endif
