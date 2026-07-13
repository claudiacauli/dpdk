#include "eval_umax_bits.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
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
	// Half-width propagation: an input under msk>>1 yields a mask under
	// msk>>1 (bit-length is monotone). The signed-track callers store
	// the result into s.max, whose invariant is <= msk>>1, not <= msk.
	ensures half32: opsz == 32 && v <= 0x7FFFFFFF ==> \result <= 0x7FFFFFFF;
	ensures half64: opsz == 64 && v <= 0x7FFFFFFFFFFFFFFF ==>
		\result <= 0x7FFFFFFFFFFFFFFF;
	ensures tight: v != 0 ==> (\result >> 1) <= v;
*/
uint64_t eval_umax_bits(uint64_t v, size_t opsz)
{
	if (v == 0)
		return 0;

	v = rte_clz64(v);
#ifdef FIX_UMAX_BITS_32
	/*
	 * rte_clz64 counts leading zeros against 64 bits, so the value's
	 * bit-length is 64 - clz INDEPENDENT of opsz — but upstream computes
	 * opsz - clz, which for opsz == 32 underflows size_t (or hits 0) for
	 * every nonzero 32-bit input, sending RTE_LEN2MASK's shift count out
	 * of [0, 63] which is Undefined Behavior (UB), and on shift-count-wrapping
	 * hardware an out-of-width bound that corrupts the tracked ranges of
	 * 32-bit AND/OR/XOR.
	 *
	 * BMC counterexample: opsz=32, v=1 -> shift by 95.
	 * For opsz == 64 this is identical to the original expression.
	 */
	return RTE_LEN2MASK(sizeof(uint64_t) * CHAR_BIT - v, uint64_t);
#else
	return RTE_LEN2MASK(opsz - v, uint64_t);
#endif
}
