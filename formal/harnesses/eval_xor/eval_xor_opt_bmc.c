/*
 * OP-OPTIMALITY probe for eval_xor — Category-B test. XOR reuses the OR
 * bit-fill bound (a^b <= a|b), so u.max = eval_uor_max(rd.u.max, rs.u.max).
 * Nondet-pair refutation on fixed self-optimal inputs:
 *   assert (a ^ b) != rd.u.max  -->  SUCCESSFUL => LOOSE, FAILED => attained.
 * Regimes: -DR_LOOSE rd=[0,8],rs=[0,4] (code 15, true max(a^b)=12);
 *          -DR_TIGHT rd=[0,8],rs=[0,8] (code 15, a=8^b=7 -> 15).
 * -DBMC_32|_64 ; -DBMC_SANITY.  Build with -DALL_FIXES.
 */
#include <assert.h>
#include "eval_xor.h"

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

#if defined(R_LOOSE)
	rd.u.min = 0; rd.u.max = 8; rd.s.min = 0; rd.s.max = 8;
	rs.u.min = 0; rs.u.max = 4; rs.s.min = 0; rs.s.max = 4;
#elif defined(R_TIGHT)
	rd.u.min = 0; rd.u.max = 8; rd.s.min = 0; rd.s.max = 8;
	rs.u.min = 0; rs.u.max = 8; rs.s.min = 0; rs.s.max = 8;
#else
# error "define a regime R_LOOSE|R_TIGHT"
#endif

	const struct bpf_reg_val od = rd, os = rs;
	eval_xor(&rd, &rs, opsz, msk);

	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(repr(&od, a, msk) && repr(&os, b, msk));

#ifdef BMC_SANITY
	assert(0);
#endif
	assert((a ^ b) <= rd.u.max);        /* soundness sanity */
	assert((a ^ b) != rd.u.max);        /* tightness: SUCCESSFUL=loose, FAILED=attained */
	return 0;
}
