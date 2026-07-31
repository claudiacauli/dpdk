#ifndef AXIOMS_OR_H
#define AXIOMS_OR_H

#include "specs.h"

/*@
axiomatic LorBounds {
	axiom lor_nonneg:
		\forall integer a, b; 0 <= a && 0 <= b ==> 0 <= (a | b);
	axiom lor_lb:
		\forall integer a, b;
		0 <= a && 0 <= b ==> a <= (a | b) && b <= (a | b);
	axiom lor_id0:
		\forall integer a; 0 <= a ==> (a | 0) == a && (0 | a) == a;
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
	axiom lor_land_distrib:
		\forall integer a, b, m;
		((a | (b & m)) & m) == ((a | b) & m);
	axiom to_signed_lor_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed((v | p) & m, m) == (v | to_signed(p, m));
	axiom to_signed_lor_both:
		\forall integer p, q, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= p <= m && 0 <= q <= m
		==> to_signed((p | q) & m, m)
			== (to_signed(p, m) | to_signed(q, m));
	axiom lor_allones_mono:
		\forall integer a, b, m1, m2;
		0 <= a <= m1 && 0 <= b <= m2 &&
		(m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0
		==> (a | b) <= (m1 | m2);
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

#endif
