#ifndef EVAL_MUL_H
#define EVAL_MUL_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*@

predicate eval_mul_signed_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                     struct bpf_reg_val nw, uint64_t msk) =
	\forall integer v, w;
		bin_witness(od, os, v, w, msk)
			==> nw.s.min <= to_signed((v * w) & msk, msk) <= nw.s.max;

predicate eval_mul_unsigned_soundness(struct bpf_reg_val od, struct bpf_reg_val os,
                                       struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		bin_witness(od, os, x, y, msk)
			==> nw.u.min <= ((x * y) & msk) <= nw.u.max;

lemma mul_usound_overflow:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(msk & (msk + 1)) == 0 &&
		0 <= od.u.min <= od.u.max && 0 <= os.u.min <= os.u.max &&
		nw.u.min <= od.u.min * os.u.min &&
		od.u.max * os.u.max <= nw.u.max &&
		od.u.max * os.u.max <= msk
		==> eval_mul_unsigned_soundness(od, os, nw, msk);

axiomatic MulSsoundOverflow {
axiom mul_ssound_overflow:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(msk & (msk + 1)) == 0 &&
		0 <= od.s.min <= od.s.max && 0 <= os.s.min <= os.s.max &&
		nw.s.min <= od.s.min * os.s.min &&
		od.s.max * os.s.max <= nw.s.max &&
		od.s.max * os.s.max <= (msk >> 1)
		==> eval_mul_signed_soundness(od, os, nw, msk);
}

lemma mul_usound_const:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		od.u.min == od.u.max && os.u.min == os.u.max &&
		nw.u.min <= ((od.u.min * os.u.min) & msk) &&
		((od.u.max * os.u.max) & msk) <= nw.u.max
		==> eval_mul_unsigned_soundness(od, os, nw, msk);

axiomatic MulSsoundConst {
axiom mul_ssound_const:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		0 <= od.u.min && od.u.max <= msk &&
		0 <= os.u.min && os.u.max <= msk &&
		od.s.min == od.s.max && os.s.min == os.s.max &&
		nw.s.min <= to_signed((od.s.min * os.s.min) & msk, msk) &&
		to_signed((od.s.max * os.s.max) & msk, msk) <= nw.s.max
		==> eval_mul_signed_soundness(od, os, nw, msk);
}

predicate eval_mul_unsigned_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                    struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x * y) & msk) == nw.u.max) &&
	(\exists integer x, y; bin_witness(od, os, x, y, msk) && ((x * y) & msk) == nw.u.min);

predicate eval_mul_signed_optimal(struct bpf_reg_val od, struct bpf_reg_val os,
                                  struct bpf_reg_val nw, uint64_t msk) =
	(\exists integer v, w; bin_witness(od, os, v, w, msk) && to_signed((v * w) & msk, msk) == nw.s.max) &&
	(\exists integer v, w; bin_witness(od, os, v, w, msk) && to_signed((v * w) & msk, msk) == nw.s.min);
*/

void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk);

#endif
