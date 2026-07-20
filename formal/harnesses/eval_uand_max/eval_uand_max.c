#include "eval_uand_max.h"
#include "../eval_umax_bits/eval_umax_bits.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
#include "../../common/axioms_and.h"

/*@
	requires opsz_ok: opsz == 32 || opsz == 64;
	requires w1: v1 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	requires w2: v2 <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	terminates \true;
	assigns \nothing;

	ensures uand_nonneg: 0 <= \result;
	ensures uand_width:  \result <= (opsz == 32 ? _32_BIT_MASK : _64_BIT_MASK);
	// Half-width propagation through the AND: the result is bounded by
	// the v2 side's mask alone (AND only clears bits), so a v2 under
	// msk>>1 pins the result under msk>>1. Both signed-track call sites
	// in eval_and satisfy the hypothesis (their v2 is masked by, or
	// literally is, msk >> 1).
	ensures uand_half32: opsz == 32 && v2 <= 0x7FFFFFFF ==>
		\result <= 0x7FFFFFFF;
	// The soundness workhorse: the result covers the AND of ANY pair
	// drawn from [0, v1] x [0, v2] — eval_and's usound/ssound
	// quantifiers instantiate this at their witnesses.
	ensures uand_cover: \forall integer a, b;
		0 <= a <= v1 && 0 <= b <= v2 ==> (a & b) <= \result;
	ensures uand_half64: opsz == 64 && v2 <= 0x7FFFFFFFFFFFFFFF ==>
		\result <= 0x7FFFFFFFFFFFFFFF;
	// OP-OPTIMALITY: value-loose by construction (Category B). \result =
	// umax_bits(v1) & umax_bits(v2), the bit-FILL AND bound behind eval_and;
	// optimal only WITHIN the bit-abstraction (via umax_bits' `optimal`), not as a
	// value bound -- optimality_notes.md §6d/§6h.
*/
uint64_t eval_uand_max(uint64_t v1, uint64_t v2, size_t opsz)
{
	v1 = eval_umax_bits(v1, opsz);
	v2 = eval_umax_bits(v2, opsz);
	return (v1 & v2);
}
