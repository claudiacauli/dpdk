#ifndef AXIOMS_AND_H
#define AXIOMS_AND_H

#include "specs.h"

/*@
axiomatic LandCanon {
	axiom land_canon_32:
		\forall integer a, b;
		-0x80000000 <= a <= 0x7FFFFFFF &&
		-0x80000000 <= b <= 0x7FFFFFFF
		==> -0x80000000 <= (a & b) <= 0x7FFFFFFF;
	axiom land_canon_64:
		\forall integer a, b;
		-0x8000000000000000 <= a <= 0x7FFFFFFFFFFFFFFF &&
		-0x8000000000000000 <= b <= 0x7FFFFFFFFFFFFFFF
		==> -0x8000000000000000 <= (a & b) <= 0x7FFFFFFFFFFFFFFF;
	axiom land_allones_mono:
		\forall integer a, b, m1, m2;
		0 <= a <= m1 && 0 <= b <= m2 &&
		(m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0
		==> (a & b) <= (m1 & m2);
	axiom land_allones_id:
		\forall integer x, m;
		0 <= x <= m && (m & (m + 1)) == 0
		==> (x & m) == x;
	axiom land_half32_id:
		\forall integer x;
		0 <= x <= 0x7FFFFFFF ==> (x & 0x7FFFFFFF) == x;
	axiom land_half64_id:
		\forall integer x;
		0 <= x <= 0x7FFFFFFFFFFFFFFF
		==> (x & 0x7FFFFFFFFFFFFFFF) == x;
	axiom land_nonneg_any:
		\forall integer a, b;
		0 <= b ==> 0 <= (a & b) <= b;
	axiom land_allones_absorb:
		\forall integer a, b, m;
		0 <= a <= m && 0 <= b && (m & (m + 1)) == 0
		==> (a & b) <= m;
	axiom to_signed_land_id_32:
		\forall integer u;
		-0x80000000 <= u <= 0x7FFFFFFF
		==> to_signed(u & 0xFFFFFFFF, 0xFFFFFFFF) == u;
	axiom to_signed_land_id_64:
		\forall integer u;
		-0x8000000000000000 <= u <= 0x7FFFFFFFFFFFFFFF
		==> to_signed(u & 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF) == u;
	axiom to_signed_land_pat:
		\forall integer v, p, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= v <= (m >> 1) && 0 <= p <= m
		==> to_signed(v & p, m) == (v & to_signed(p, m));
	axiom to_signed_land_both:
		\forall integer p, q, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		0 <= p <= m && 0 <= q <= m
		==> to_signed(p & q, m)
			== (to_signed(p, m) & to_signed(q, m));
	axiom to_signed_pattern_id:
		\forall integer w, m;
		(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
		-(m >> 1) - 1 <= w <= (m >> 1)
		==> to_signed(w & m, m) == w;
	axiom land_absorb_window:
		\forall integer v, y, m;
		0 <= v <= m && (m & (m + 1)) == 0 && 0 <= y
		==> (v & y) == (v & (y & m));
}
*/

#endif
