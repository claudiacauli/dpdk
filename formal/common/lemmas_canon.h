#ifndef LEMMAS_CANON_H
#define LEMMAS_CANON_H

#include "specs.h"

/*@
lemma to_signed_canon_rt:
	\forall integer w, m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	-(m >> 1) - 1 <= w <= (m >> 1)
	==> to_signed(((uint64_t)w) & m, m) == w;
*/

#endif
