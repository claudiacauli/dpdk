#include "eval_uor_max.h"
#include "../eval_umax_bits/eval_umax_bits.h"

#include "../../common/axioms_or.h"

/*@
	requires opsz_ok: opsz == 32 || opsz == 64;
	requires w1: v1 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	requires w2: v2 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	terminates \true;
	assigns \nothing;

	ensures uor_nonneg: 0 <= \result;
	ensures uor_width:  \result <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	ensures uor_lb: v1 <= \result && v2 <= \result;
	ensures uor_half32: opsz == 32 && v1 <= 0x7FFFFFFF && v2 <= 0x7FFFFFFF ==>
		\result <= 0x7FFFFFFF;
	ensures uor_cover: \forall integer a, b;
		0 <= a <= v1 && 0 <= b <= v2 ==> (a | b) <= \result;
	ensures uor_half64: opsz == 64 && v1 <= 0x7FFFFFFFFFFFFFFF &&
		v2 <= 0x7FFFFFFFFFFFFFFF ==> \result <= 0x7FFFFFFFFFFFFFFF;
*/
uint64_t eval_uor_max(uint64_t v1, uint64_t v2, size_t opsz)
{
	v1 = eval_umax_bits(v1, opsz);
	v2 = eval_umax_bits(v2, opsz);
	return (v1 | v2);
}
