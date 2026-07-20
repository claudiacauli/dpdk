#include "eval_uor_max.h"
#include "../eval_umax_bits/eval_umax_bits.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
#include "../../common/axioms_or.h"

/*@
	requires opsz_ok: opsz == 32 || opsz == 64;
	requires w1: v1 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	requires w2: v2 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	terminates \true;
	assigns \nothing;

	ensures uor_nonneg: 0 <= \result;
	ensures uor_width:  \result <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	// The result covers each input: eval_umax_bits widens vi to a mask
	// Mi >= vi, and OR only sets bits, so vi <= Mi <= M1|M2 == \result.
	// eval_or's range-ordering and lower-bound soundness lean on this
	// (the new u.min/s.min are RTE_MAX of the old mins, still <= result).
	ensures uor_lb: v1 <= \result && v2 <= \result;
	// Half-width propagation through the OR. Unlike eval_uand_max, a single
	// bounded side is NOT enough: OR only SETS bits, so an input with bit
	// w-1 set would set it in the result. The result stays under msk>>1
	// only when BOTH inputs do. eval_or's signed track satisfies this — it
	// calls with rd->s.max, rs->s.max under rd->s.min>=0 && rs->s.min>=0,
	// so both are canonical non-negative maxes bounded by msk>>1.
	ensures uor_half32: opsz == 32 && v1 <= 0x7FFFFFFF && v2 <= 0x7FFFFFFF ==>
		\result <= 0x7FFFFFFF;
	// The soundness workhorse: the result covers the OR of ANY pair drawn
	// from [0, v1] x [0, v2] — and hence the XOR too, since a^b <= a|b, so
	// this single ensures backs both eval_or and eval_xor. It holds because
	// eval_umax_bits widens each input to the all-ones mask 2^k-1 that just
	// covers it, and a<=v1<=M1, b<=v2<=M2 keep every bit of a|b inside the
	// union window M1|M2 == \result.
	ensures uor_cover: \forall integer a, b;
		0 <= a <= v1 && 0 <= b <= v2 ==> (a | b) <= \result;
	ensures uor_half64: opsz == 64 && v1 <= 0x7FFFFFFFFFFFFFFF &&
		v2 <= 0x7FFFFFFFFFFFFFFF ==> \result <= 0x7FFFFFFFFFFFFFFF;
	// OP-OPTIMALITY: value-loose by construction (Category B). \result =
	// umax_bits(v1) | umax_bits(v2), the bit-FILL OR bound behind eval_or/eval_xor;
	// optimal only WITHIN the bit-abstraction (via umax_bits' `optimal`), not as a
	// value bound -- optimality_notes.md §6d/§6h.
*/
uint64_t eval_uor_max(uint64_t v1, uint64_t v2, size_t opsz)
{
	v1 = eval_umax_bits(v1, opsz);
	v2 = eval_umax_bits(v2, opsz);
	return (v1 | v2);
}
