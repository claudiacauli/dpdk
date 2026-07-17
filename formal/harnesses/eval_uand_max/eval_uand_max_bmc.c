#include <assert.h>
#include "eval_uand_max.h"

uint64_t nondet_u64(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/*
 * Intended contract, derived from the call sites in bpf_validate.c
 * (eval_and / eval_or / eval_xor non-constant branches, which feed the
 * result straight into rd->u.max / rd->s.max): eval_uand_max(v1, v2)
 * over-approximates the AND of any pair drawn from [0, v1] x [0, v2].
 *
 *   uand_nonneg: 0 <= result            (trivial in uint64; stated for
 *                                        parity with the ACSL ensures)
 *   uand_width:  result <= 2^opsz - 1   (register width invariant)
 *   uand_cover:  a <= v1 && b <= v2 ==> (a & b) <= result
 *   uand_shape:  result is 2^k - 1      (AND of two all-ones masks)
 *   uand_tight:  result >> 1 <= v1 || result >> 1 <= v2
 *                                       (the smaller side's mask is at
 *                                        most one bit-length over)
 *
 * Callers guarantee v1, v2 <= 2^opsz - 1 (u.max via uwidth, or
 * s.max & (msk >> 1), or the literal msk >> 1 under
 * FIX_AND_SIGNED_GUARD). Build with -DALL_FIXES: without
 * FIX_UMAX_BITS_32 the callee is UB for opsz == 32 and everything here
 * fails on that instead.
 */
int main(void)
{
	size_t opsz = nondet_size_t();
	REQUIRE(opsz == 32 || opsz == 64);

	uint64_t msk = (opsz == 32) ? UINT32_MAX : UINT64_MAX;

	uint64_t v1 = nondet_u64(), v2 = nondet_u64();
	REQUIRE(v1 <= msk && v2 <= msk);

	/* concrete witnesses for the \forall a, b of uand_cover */
	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(a <= v1 && b <= v2);

	uint64_t r = eval_uand_max(v1, v2, opsz);

	assert(0 <= r);                                /* uand_nonneg */
	assert(r <= msk);                              /* uand_width  */
	assert((a & b) <= r);                          /* uand_cover  */
	assert((r & (r + 1)) == 0);                    /* uand_shape  */
	assert((r >> 1) <= v1 || (r >> 1) <= v2);      /* uand_tight  */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
