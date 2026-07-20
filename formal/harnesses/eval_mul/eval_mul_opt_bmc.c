/*
 * OP-OPTIMALITY probe for eval_mul (nonlinear -> concrete small regimes,
 * like the bitwise ops). mul's non-widen path is corner-based:
 *   both-nonneg, no overflow: u.max=rd.u.max*rs.u.max, u.min=rd.u.min*rs.u.min
 *   (same for s). Products are monotone on non-negatives, so the corners give
 *   the extremes -> should be tight. But mul only handles BOTH-NONNEG for the
 *   signed track; mixed signs / overflow WIDEN (loose).
 *
 * R_NONNEG: rd=[2,3], rs=[4,5]  (small, both non-neg; corner products fit)
 *   nondet-pair refutation per endpoint:
 *     assert result != endpoint -> SUCCESSFUL=loose, FAILED(CEX)=attained/tight.
 * R_MIXED_OUT: rd s=[-3,-2] (neg), rs s=[2,3] -> signed track WIDENS; we just
 *   assert the output s.max == msk>>1 (INT_MAX) to show it widened (true max -4).
 *
 * Flags: -DBMC_UMAX|_UMIN|_SMAX|_SMIN (R_NONNEG); -DR_MIXED_OUT; -DBMC_32|_64;
 *        -DBMC_SANITY.  Build with -DALL_FIXES.
 */
#include <assert.h>
#include "eval_mul.h"

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
	uint64_t msk; size_t opsz;
#ifdef BMC_32
	msk = _32_BIT_MASK; opsz = 32;
#else
	msk = _64_BIT_MASK; opsz = 64;
#endif
	struct bpf_reg_val rd, rs;
	rd.v.type = rs.v.type = RTE_BPF_ARG_RAW;
	rd.v.size = rs.v.size = 0; rd.v.buf_size = rs.v.buf_size = 0;
	rd.mask = rs.mask = msk;

#ifdef R_MIXED_OUT
	/* rd negative, rs positive: signed multiply, both-nonneg guard fails */
	rd.u.min = (msk - 2); rd.u.max = (msk - 1); rd.s.min = -3; rd.s.max = -2;
	rs.u.min = 2; rs.u.max = 3; rs.s.min = 2; rs.s.max = 3;
	eval_mul(&rd, &rs, opsz, msk);
	/* true signed product range is [-9,-4]; show the code widened s.max to INT_MAX */
	assert(rd.s.max == (int64_t)(msk >> 1));   /* holds => widened => LOOSE */
	return 0;
#else
	/* R_NONNEG small self-optimal both-non-negative */
	rd.u.min = 2; rd.u.max = 3; rd.s.min = 2; rd.s.max = 3;
	rs.u.min = 4; rs.u.max = 5; rs.s.min = 4; rs.s.max = 5;

	const struct bpf_reg_val od = rd, os = rs;
	eval_mul(&rd, &rs, opsz, msk);

	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(repr(&od, a, msk) && repr(&os, b, msk));

  #ifdef BMC_SANITY
	assert(0);
  #endif
	uint64_t ures = (a * b) & msk;
	int64_t  sres = tos(ures, msk);
	assert(ures <= rd.u.max);              /* soundness sanity */
  #if defined(BMC_UMAX)
	assert(ures != rd.u.max);
  #elif defined(BMC_UMIN)
	assert(ures != rd.u.min);
  #elif defined(BMC_SMAX)
	assert(sres != rd.s.max);
  #elif defined(BMC_SMIN)
	assert(sres != rd.s.min);
  #else
	#error "define a BMC_* endpoint or R_MIXED_OUT"
  #endif
	return 0;
#endif
}
