#ifndef LEMMAS_CANON_LSH_H
#define LEMMAS_CANON_LSH_H

#include "../../common/specs.h"
#include "eval_lsh.h"

/*@
lemma to_signed_canon_shift_rt:
	\forall integer w, y, m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) &&
	0 <= w <= m && 0 <= y &&
	(w << y) <= (m >> 1)
	==> to_signed(((((uint64_t)w) & m) << y) & m, m) == (w << y);
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

#endif
