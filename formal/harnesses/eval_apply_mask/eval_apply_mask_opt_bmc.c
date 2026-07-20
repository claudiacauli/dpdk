/*
 * OP-OPTIMALITY probe for eval_apply_mask (narrow a register to `mask`
 * bits: value set becomes {v & mask}). Unary; nondet-value refutation on u.max:
 *   assert (v & mask) != rv.u.max  ->  SUCCESSFUL=loose, FAILED(CEX)=attained.
 * Regimes (self-optimal):
 *   -DR_ID64     : 64-bit mask, u=[5,10]           (identity -> tight)
 *   -DR_FIT32    : 32-bit mask, u=[5,10] (fits)    (kept -> tight)
 *   -DR_STRADDLE : 32-bit mask, u=[2^32, 2^32+5]   (exceeds -> u widens to [0,mask];
 *                                                   masked set {0..5}, so u.max=mask LOOSE)
 * -DBMC_SANITY.  Build with -DALL_FIXES.
 */
#include <assert.h>
#include "eval_apply_mask.h"

uint64_t nondet_u64(void);
#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
}
static int repr(const struct bpf_reg_val *o, uint64_t x, uint64_t msk)
{
	return o->u.min <= x && x <= o->u.max &&
	       o->s.min <= tos(x, msk) && tos(x, msk) <= o->s.max;
}

int main(void)
{
	uint64_t mask;
	struct bpf_reg_val rv;
	rv.v.type = RTE_BPF_ARG_RAW; rv.v.size = 0; rv.v.buf_size = 0;

#if defined(R_ID64)
	mask = _64_BIT_MASK;
	rv.u.min = 5; rv.u.max = 10; rv.s.min = 5; rv.s.max = 10;
#elif defined(R_FIT32)
	mask = _32_BIT_MASK;
	rv.u.min = 5; rv.u.max = 10; rv.s.min = 5; rv.s.max = 10;
#elif defined(R_STRADDLE)
	mask = _32_BIT_MASK;
	rv.u.min = 0x100000000ULL; rv.u.max = 0x100000005ULL;   /* 2^32 .. 2^32+5 */
	rv.s.min = 0x100000000LL;  rv.s.max = 0x100000005LL;    /* readings positive (< 2^63) */
#else
# error "define a regime R_ID64|R_FIT32|R_STRADDLE"
#endif
	rv.mask = mask;

	/* value semantics use the FULL 64-bit reading of the input patterns */
	const struct bpf_reg_val od = rv;
	eval_apply_mask(&rv, mask);

	uint64_t v = nondet_u64();
	/* v is an input pattern in the register (read against 64-bit width) */
	REQUIRE(repr(&od, v, _64_BIT_MASK));

#ifdef BMC_SANITY
	assert(0);
#endif
	uint64_t res = v & mask;             /* masked value */
	assert(res <= rv.u.max);             /* soundness sanity */
	assert(res != rv.u.max);             /* u.max: SUCCESSFUL=loose, FAILED=attained */
	return 0;
}
