#ifndef LEMMAS_CANON_LSH_H
#define LEMMAS_CANON_LSH_H

#include "../../common/specs.h"

/*
 * lsh-shaped round-trip lemma (2026-07-20, dump-diagnosed). The shared
 * to_signed_canon_rt (common/lemmas_canon.h) can NEVER fire on lsh's
 * ssound conclusion: its application term demands a to_uint64 node
 * directly under the land under to_signed, but lsh's term is
 *
 *     to_signed( land(m, lsl( land(m, to_uint64(w)), y )), m )
 *
 * -- the lsl sits between the two lands, and no to_uint64 e-node equal
 * to that lsl exists anywhere in the PO. This lemma's application term
 * is character-for-character the ssound predicate's term shape
 * (eval_lsh.h), so it collapses the whole bit-level chain to the plain
 * integer w << y; the residue is linear arithmetic plus one
 * lsl_both_mono firing per bound -- the same steps the green parts do.
 *
 * TU-scoped to lsh ON PURPOSE: not in common/lemmas_canon.h, because
 * arsh sits on a 97-part cliff and extra quantified hypotheses in a
 * shared header have a measured cost there. Proved in the driver's
 * shift-opt @lemma pass (whose TU list includes eval_lsh.c).
 *
 * Truth: (w << y) <= m >> 1 forces w <= m >> 1, both lands strip, and
 * to_signed is the identity on canonical values. WP-provable from
 * axioms.h alone -- no new trust burden.
 */
/*@
lemma to_signed_canon_shift_rt:
	\forall integer w, y, m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	0 <= w <= m && 0 <= y &&
	(w << y) <= (m >> 1)
	==> to_signed(((((uint64_t)w) & m) << y) & m, m) == (w << y);
*/

#endif /* LEMMAS_CANON_LSH_H */
