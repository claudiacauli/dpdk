#ifndef LEMMAS_CANON_ARSH_H
#define LEMMAS_CANON_ARSH_H

#include "eval_arsh.h"

/*@
lemma arsh_usound_neg32:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFF &&
	0x80000000 <= od.u.min && od.u.min <= od.u.max && od.u.max <= msk &&
	os.u.min <= os.u.max && os.u.max <= 31 &&
	nw.u.min == (((uint64_t)(to_signed(od.u.min, msk) >> os.u.min)) & msk) &&
	nw.u.max == (((uint64_t)(to_signed(od.u.max, msk) >> os.u.max)) & msk)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_neg64:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFFFFFFFFFF &&
	0x8000000000000000 <= od.u.min && od.u.min <= od.u.max &&
	os.u.min <= os.u.max && os.u.max <= 63 &&
	nw.u.min == (((uint64_t)(to_signed(od.u.min, msk) >> os.u.min)) & msk) &&
	nw.u.max == (((uint64_t)(to_signed(od.u.max, msk) >> os.u.max)) & msk)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_pos32:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFF &&
	od.u.min <= od.u.max && od.u.max <= (msk >> 1) &&
	os.u.min <= os.u.max && os.u.max <= 31 &&
	nw.u.min == (od.u.min >> os.u.max) &&
	nw.u.max == (od.u.max >> os.u.min)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_pos64:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFFFFFFFFFF &&
	od.u.min <= od.u.max && od.u.max <= (msk >> 1) &&
	os.u.min <= os.u.max && os.u.max <= 63 &&
	nw.u.min == (od.u.min >> os.u.max) &&
	nw.u.max == (od.u.max >> os.u.min)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);
*/

#endif
