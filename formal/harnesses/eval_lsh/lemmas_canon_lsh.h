#ifndef LEMMAS_CANON_LSH_H
#define LEMMAS_CANON_LSH_H

#include "../../common/specs.h"
#include "eval_lsh.h"

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

/*
 * FOLDED shift-branch soundness lemmas (2026-07-28, dump-diagnosed).
 * The four red split parts (usound 10/11, ssound 06/11) are exactly the
 * parts whose track was SHIFTED, not widened: their conclusion is the
 * folded soundness predicate, and the in-context search — unfold,
 * skolemize the witness pair, unfold bin_witness, chain lsl_both_mono,
 * strip the lands under the mask case split — dies among ~50 hypotheses
 * even at 1800s. Same remedy as eval_mul's mul_usound_overflow (the
 * PROVED precedent): state each shift branch's soundness against the
 * folded predicate with bracket hypotheses in the EXACT stored term
 * shapes (masked lsl for the u-track, plain int64 lsl for the s-track,
 * per the uopt_sum_* / s*_shift_id stones), so each red part closes by
 * ONE instantiation whose hypotheses discharge reflexively.
 *
 * Truth, and why THESE prove where the mul ssound lemmas did not: the
 * nonlinear core is delegated to the trusted LenShift axioms
 * (lsl_both_mono, lsl_nonneg) and the canon round-trip above — the
 * lemma PO itself is e-matching plus linear residue, the same class as
 * mul_usound_overflow (proved), not mul's raw-NIA signed statements
 * (axiomatized). usound: witnesses sit between the corner shifts by
 * lsl_both_mono; the corner shift is <= msk by hypothesis, so every
 * land strips. ssound: 0 <= s.min forces every witness decode
 * non-negative, so pattern == value (v <= msk from od.u.max <= msk),
 * the corner bound (s.max << q.max) <= msk >> 1 lets
 * to_signed_canon_shift_rt collapse the image term to v << y, and
 * lsl_both_mono brackets it.
 */
/*@
lemma lsh_usound_shift:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	od.u.min <= od.u.max && os.u.min <= os.u.max &&
	(od.u.max << os.u.max) <= msk &&
	nw.u.min <= ((od.u.min << os.u.min) & msk) &&
	((od.u.max << os.u.max) & msk) <= nw.u.max
	==> eval_lsh_unsigned_soundness(od, os, nw, msk);

lemma lsh_ssound_shift:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	0 <= od.s.min && od.s.min <= od.s.max &&
	os.u.min <= os.u.max &&
	od.u.max <= msk &&
	(od.s.max << os.u.max) <= (msk >> 1) &&
	nw.s.min <= (od.s.min << os.u.min) &&
	(od.s.max << os.u.max) <= nw.s.max
	==> eval_lsh_signed_soundness(od, os, nw, msk);
*/

#endif /* LEMMAS_CANON_LSH_H */
