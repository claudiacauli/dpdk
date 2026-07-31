#ifndef AXIOMS_XOR_H
#define AXIOMS_XOR_H

#include "../../common/specs.h"

/*@
axiomatic LxorBounds {
	axiom lxor_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a ^ b);
	axiom lxor_le_lor:
		\forall integer a, b; 0 <= a && 0 <= b ==> (a ^ b) <= (a | b);
	axiom lxor_mask32:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
		==> (a ^ b) <= 0xFFFFFFFF;
	axiom lxor_mask64:
		\forall integer a, b;
		0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
		==> (a ^ b) <= 0xFFFFFFFFFFFFFFFF;
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
	axiom to_signed_lxor_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed((v ^ p) & m, m) == (v ^ to_signed(p, m));
	axiom to_signed_lxor_both:
		\forall integer p, q, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= p <= m && 0 <= q <= m
		==> to_signed((p ^ q) & m, m)
			== (to_signed(p, m) ^ to_signed(q, m));
}
*/

#endif
