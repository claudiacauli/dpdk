#include "eval_umax_bits.h"

#include "axioms_clz.h"

/*@
	requires opsz == 32 || opsz == 64;
	requires v <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	terminates \true;
	assigns \nothing;

	ensures zero:  v == 0 ==> \result == 0;
	ensures cover: v <= \result;
	ensures shape: (\result & (\result + 1)) == 0;
	ensures width: \result <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	ensures half32: opsz == 32 && v <= 0x7FFFFFFF ==> \result <= 0x7FFFFFFF;
	ensures half64: opsz == 64 && v <= 0x7FFFFFFFFFFFFFFF ==>
		\result <= 0x7FFFFFFFFFFFFFFF;
	ensures optimal: v != 0 ==> (\result >> 1) <= v;
*/
uint64_t eval_umax_bits(uint64_t v, size_t opsz)
{
	if (v == 0)
		return 0;

	v = rte_clz64(v);
#ifdef FIX_UMAX_BITS_32

	return RTE_LEN2MASK(sizeof(uint64_t) * CHAR_BIT - v, uint64_t);
#else
	return RTE_LEN2MASK(opsz - v, uint64_t);
#endif
}
