#ifndef AXIOMS_ARSH_H
#define AXIOMS_ARSH_H

#include "../../common/shared.h"

/*@
axiomatic ArshShift {
	axiom asr_val_mono:
		\forall integer a, b, y;
		a <= b && 0 <= y ==> (a >> y) <= (b >> y);
	axiom asr_amt_mono_neg:
		\forall integer x, p, q;
		x < 0 && 0 <= p <= q ==> (x >> p) <= (x >> q);
	axiom asr_neg_bounds:
		\forall integer x, y;
		x < 0 && 0 <= y ==> x <= (x >> y) <= -1;
	axiom asr_both_neg:
		\forall integer a, b, p, q;
		a <= b && b < 0 && 0 <= p <= q ==> (a >> p) <= (b >> q);
	axiom shl32_ext_id:
		\forall int64_t v;
		-0x80000000 <= v < 0x80000000 ==>
		(int64_t)(((uint64_t)v) << 32) == v * 0x100000000;
	axiom asr_descale32:
		\forall integer v, w;
		-0x80000000 <= v < 0x80000000 && 32 <= w <= 63 ==>
		((v * 0x100000000) >> w) == (v >> (w - 32));
}
*/

#endif
