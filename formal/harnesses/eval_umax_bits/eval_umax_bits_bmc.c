#include <assert.h>
#include "eval_umax_bits.h"

uint64_t nondet_u64(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/*
 * Intended contract, derived from the call sites in bpf_validate.c
 * (eval_uand_max / eval_uor_max, backing eval_and / eval_or / eval_xor):
 * eval_umax_bits(v, opsz) rounds an upper bound v up to the tightest
 * all-ones mask 2^bitlen(v) - 1. The callers' soundness argument needs:
 *
 *   zero:   v == 0 implies result == 0
 *   cover:  v <= result           (a <= v implies bits(a) within mask)
 *   shape:  result is 2^k - 1     (so mask1 & mask2 / mask1 | mask2 of
 *                                  two covers still cover a&b / a|b)
 *   width:  result <= 2^opsz - 1  (the register width invariant)
 *   tight:  result >> 1 <= v      (completeness: at most one bit-length
 *                                  over; overflow-free form of
 *                                  result <= 2*v + 1)
 *
 * EXPECTED FAILURES for opsz == 32: the implementation computes
 * RTE_LEN2MASK(opsz - rte_clz64(v)) but rte_clz64 counts against 64
 * bits, so for every valid 32-bit v != 0 the length underflows size_t
 * (or is 0), and the macro's shift count leaves [0, 63] — undefined
 * behaviour, and garbage bounds on machines that wrap the shift count.
 * The correct length is 64 - rte_clz64(v), independent of opsz.
 * The opsz == 64 path is expected to verify.
 */
int main(void)
{
	size_t opsz = nondet_size_t();
	REQUIRE(opsz == 32 || opsz == 64);

	uint64_t msk = (opsz == 32) ? UINT32_MAX : UINT64_MAX;

	/* callers pass u.max (<= msk by uwidth) or s.max & (msk >> 1) */
	uint64_t v = nondet_u64();
	REQUIRE(v <= msk);

	uint64_t r = eval_umax_bits(v, opsz);

	if (v == 0)
		assert(r == 0);                        /* zero  */
	assert(v <= r);                                /* cover */
	assert((r & (r + 1)) == 0);                    /* shape */
	assert(r <= msk);                              /* width */
	if (v != 0)
		assert((r >> 1) <= v);                 /* tight */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
