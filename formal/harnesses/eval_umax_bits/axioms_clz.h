#ifndef AXIOMS_CLZ_H
#define AXIOMS_CLZ_H

#include "../../common/shared.h"

/*@
axiomatic ClzWindow {

	axiom clz_window_hi:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> v <= (_64_BIT_MASK >> r);

	axiom clz_window_lo:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1
		==> ((_64_BIT_MASK >> r) >> 1) < v;

	axiom allones_shr_shape:
		\forall integer r;
		0 <= r <= 63
		==> ((_64_BIT_MASK >> r) & ((_64_BIT_MASK >> r) + 1)) == 0;

	axiom clz_mask_width_32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= _32_BIT_MASK
		==> (_64_BIT_MASK >> r) <= _32_BIT_MASK;

	axiom clz_mask_half32:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFF
		==> (_64_BIT_MASK >> r) <= 0x7FFFFFFF;

	axiom clz_mask_half64:
		\forall integer v, r;
		0 <= v && 0 <= r <= 63 && (v >> (63 - r)) == 1 &&
		v <= 0x7FFFFFFFFFFFFFFF
		==> (_64_BIT_MASK >> r) <= 0x7FFFFFFFFFFFFFFF;
}
*/

#endif
