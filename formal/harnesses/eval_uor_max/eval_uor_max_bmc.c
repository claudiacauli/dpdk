#include <assert.h>
#include "eval_uor_max.h"

uint64_t nondet_u64(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/*
 * Intended contract, derived from the call sites in bpf_validate.c
 * (eval_or / eval_xor non-constant branches, which feed the result
 * straight into rd->u.max / rd->s.max): eval_uor_max(v1, v2)
 * over-approximates the OR of any pair drawn from [0, v1] x [0, v2] —
 * and therefore the XOR of the same pair, since a ^ b <= a | b.
 *
 *   uor_nonneg: 0 <= result             (trivial in uint64; stated for
 *                                         parity with the ACSL ensures)
 *   uor_width:  result <= 2^opsz - 1    (register width invariant)
 *   uor_cover:  a <= v1 && b <= v2 ==> (a | b) <= result
 *               (and (a ^ b) <= result, the eval_xor caller)
 *   uor_half:   v1 <= msk>>1 && v2 <= msk>>1 ==> result <= msk>>1
 *               (OR sets bits, so BOTH sides must be bounded — contrast
 *                eval_uand_max, where one bounded side suffices)
 *   uor_shape:  result is 2^k - 1       (OR of two all-ones masks is the
 *                                         wider all-ones mask)
 *   uor_tight:  result >> 1 <= v1 || result >> 1 <= v2
 *                                        (the wider mask is at most one
 *                                         bit-length over its own input)
 *
 * Callers guarantee v1, v2 <= 2^opsz - 1 (u.max via uwidth, or the
 * canonical non-negative s.max <= msk>>1 under the s.min>=0 guard).
 * Build with -DALL_FIXES: without FIX_UMAX_BITS_32 the callee is UB for
 * opsz == 32 and everything here fails on that instead.
 */
int main(void)
{
	size_t opsz = nondet_size_t();
	REQUIRE(opsz == 32 || opsz == 64);

	uint64_t msk = (opsz == 32) ? UINT32_MAX : UINT64_MAX;

	uint64_t v1 = nondet_u64(), v2 = nondet_u64();
	REQUIRE(v1 <= msk && v2 <= msk);

	/* concrete witnesses for the \forall a, b of uor_cover */
	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(a <= v1 && b <= v2);

	uint64_t r = eval_uor_max(v1, v2, opsz);

	assert(0 <= r);                                /* uor_nonneg */
	assert(r <= msk);                              /* uor_width  */
	assert((a | b) <= r);                          /* uor_cover  */
	assert((a ^ b) <= r);                          /* uor_cover (xor caller) */
	assert((r & (r + 1)) == 0);                    /* uor_shape  */
	assert((r >> 1) <= v1 || (r >> 1) <= v2);      /* uor_tight  */

	/* half-width: BOTH sides bounded, because OR sets bits */
	if (v1 <= (msk >> 1) && v2 <= (msk >> 1))
		assert(r <= (msk >> 1));               /* uor_half   */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
