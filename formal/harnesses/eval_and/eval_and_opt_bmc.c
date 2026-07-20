/*
 * OP-OPTIMALITY probe for eval_and — the Category-B test.
 *
 * AND's u.max is eval_uand_max = umax_bits(v1) & umax_bits(v2): each operand max
 * is rounded UP to 2^k-1 (bit-fill) then ANDed. The tight max of a&b over the
 * ranges depends on the achievable BIT PATTERNS, not just the endpoints, so
 * (a) the bit-fill bound overshoots and (b) there is no cheap endpoint formula
 * for the true max. This probe fixes a concrete SELF-OPTIMAL input and asks, over a
 * nondet representable pair (a,b), whether the computed u.max is ever attained:
 *
 *   assert (a & b) != rd.u.max   -->
 *     VERIFICATION SUCCESSFUL => NO pair attains u.max => LOOSE (with soundness
 *                                a&b<=u.max, u.max is strictly above the image).
 *     VERIFICATION FAILED (CEX) => some pair hits u.max => tight for this input.
 *
 * Regimes (all self-optimal, non-negative — u-track focus):
 *   -DR_DISJOINT : rd=const 8, rs=[0,7]      (bits disjoint; true max 0, code 7)
 *   -DR_FILL     : rd=[0,8],   rs=[0,8]       (true max 8, code 15)
 *   -DR_ONES     : rd=[0,7],   rs=[0,7]       (2^k-1 forms; true max 7 == code 7)
 * -DBMC_32|_64 ; -DBMC_SANITY.  Build with -DALL_FIXES.
 */
#include <assert.h>
#include "eval_and.h"

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

#if defined(R_DISJOINT)
	rd.u.min = 8; rd.u.max = 8; rd.s.min = 8; rd.s.max = 8;
	rs.u.min = 0; rs.u.max = 7; rs.s.min = 0; rs.s.max = 7;
#elif defined(R_FILL)
	rd.u.min = 0; rd.u.max = 8; rd.s.min = 0; rd.s.max = 8;
	rs.u.min = 0; rs.u.max = 8; rs.s.min = 0; rs.s.max = 8;
#elif defined(R_ONES)
	rd.u.min = 0; rd.u.max = 7; rd.s.min = 0; rd.s.max = 7;
	rs.u.min = 0; rs.u.max = 7; rs.s.min = 0; rs.s.max = 7;
#else
# error "define a regime R_DISJOINT|R_FILL|R_ONES"
#endif

	/* inputs are self-optimal by construction (small non-negative ranges) */
	const struct bpf_reg_val od = rd, os = rs;
	eval_and(&rd, &rs, opsz, msk);

	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(repr(&od, a, msk) && repr(&os, b, msk));

#ifdef BMC_SANITY
	assert(0);
#endif
	/* soundness sanity: the image is under u.max (should always hold) */
	assert((a & b) <= rd.u.max);
	/* tightness: is u.max attained? SUCCESSFUL => loose, FAILED => attained */
	assert((a & b) != rd.u.max);
	return 0;
}
