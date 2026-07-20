/*
 * OP-OPTIMALITY probe for eval_divmod (concrete small regimes).
 * Non-constant u.max: MOD -> min(rd.u.max, rs.u.max-1) (standard remainder bound);
 * DIV -> rd.u.max UNCHANGED (as if dividing by 1 — ignores the minimum divisor).
 * x/y is monotone up in x, down in y, so the tight DIV max is rd.u.max/rs.u.min.
 * Nondet-pair refutation on u.max:  assert result != rd.u.max
 *   SUCCESSFUL => LOOSE (not attained) ; FAILED(CEX) => attained (tight).
 * Regimes (self-optimal, non-negative):
 *   -DR_DIV_LOOSE : DIV rd=[0,100], rs=[2,4]  (code u.max 100; true 100/2=50)
 *   -DR_DIV_TIGHT : DIV rd=[0,100], rs=[1,4]  (divisor can be 1; true 100)
 *   -DR_MOD       : MOD rd=[0,100], rs=[3,7]  (code 6; true 6)
 * -DBMC_32|_64 ; -DBMC_SANITY.  Build with -DALL_FIXES.
 */
#include <assert.h>
#include "eval_divmod.h"

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
	uint64_t msk;
#ifdef BMC_32
	msk = _32_BIT_MASK;
#else
	msk = _64_BIT_MASK;
#endif
	struct bpf_reg_val rd, rs;
	rd.v.type = rs.v.type = RTE_BPF_ARG_RAW;
	rd.v.size = rs.v.size = 0; rd.v.buf_size = rs.v.buf_size = 0;
	rd.mask = rs.mask = msk;
	uint32_t op;

#if defined(R_DIV_LOOSE)
	op = BPF_DIV; rd.u.min = 0; rd.u.max = 100; rd.s.min = 0; rd.s.max = 100;
	rs.u.min = 2; rs.u.max = 4; rs.s.min = 2; rs.s.max = 4;
#elif defined(R_DIV_TIGHT)
	op = BPF_DIV; rd.u.min = 0; rd.u.max = 100; rd.s.min = 0; rd.s.max = 100;
	rs.u.min = 1; rs.u.max = 4; rs.s.min = 1; rs.s.max = 4;
#elif defined(R_MOD)
	op = BPF_MOD; rd.u.min = 0; rd.u.max = 100; rd.s.min = 0; rd.s.max = 100;
	rs.u.min = 3; rs.u.max = 7; rs.s.min = 3; rs.s.max = 7;
#else
# error "define a regime R_DIV_LOOSE|R_DIV_TIGHT|R_MOD"
#endif

	const struct bpf_reg_val od = rd, os = rs;
	const char *err = eval_divmod(op, &rd, &rs, msk);
	REQUIRE(err == 0);

	uint64_t x = nondet_u64(), y = nondet_u64();
	REQUIRE(repr(&od, x, msk) && repr(&os, y, msk));
	REQUIRE(y >= 1);

#ifdef BMC_SANITY
	assert(0);
#endif
	uint64_t res = (op == BPF_DIV) ? (x / y) : (x % y);
	assert(res <= rd.u.max);            /* soundness sanity */
	assert(res != rd.u.max);            /* u.max: SUCCESSFUL=loose, FAILED=attained */
	return 0;
}
