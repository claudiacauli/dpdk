
#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
}
static int repr(const struct bpf_reg_val *od, uint64_t x, uint64_t msk)
{
	return od->u.min <= x && x <= od->u.max &&
	       od->s.min <= tos(x, msk) && tos(x, msk) <= od->s.max;
}
static uint64_t pre(uint64_t m, uint64_t msk)
{
	return (m == 0) ? 0 : (msk + 1 - m);
}

int main(void)
{
	uint64_t msk;
	size_t opsz;
#ifdef BMC_32
	msk = _32_BIT_MASK; opsz = 32;
#else
	msk = _64_BIT_MASK; opsz = 64;
#endif

	struct bpf_reg_val rd;
	rd.v.type = RTE_BPF_ARG_RAW;
	rd.v.size = 0;
	rd.v.buf_size = 0;
	rd.mask = msk;
	rd.s.min = nondet_i64();
	rd.s.max = nondet_i64();
	rd.u.min = nondet_u64();
	rd.u.max = nondet_u64();

	REQUIRE(rd.u.min <= rd.u.max);
	REQUIRE(rd.s.min <= rd.s.max);
	REQUIRE(rd.u.max <= msk);
	REQUIRE(-(int64_t)(msk >> 1) - 1 <= rd.s.min && rd.s.max <= (int64_t)(msk >> 1));

#ifndef BMC_NOAGREE
	int det = rd.s.min >= 0 || rd.s.max < 0 ||
	          rd.u.min > (msk >> 1) || rd.u.max <= (msk >> 1);
	if (det) {
		REQUIRE(rd.u.min == ((uint64_t)rd.s.min & msk));
		REQUIRE(rd.u.max == ((uint64_t)rd.s.max & msk));
	}
#endif

	REQUIRE(repr(&rd, rd.u.min, msk));
	REQUIRE(repr(&rd, rd.u.max, msk));
	REQUIRE(repr(&rd, (uint64_t)rd.s.min & msk, msk));
	REQUIRE(repr(&rd, (uint64_t)rd.s.max & msk, msk));

#ifdef BMC_NOWRAP

	REQUIRE(rd.s.min != -(int64_t)(msk >> 1) - 1);
#endif

#ifdef BMC_SANITY
	assert(0);
#endif

	const struct bpf_reg_val od = rd;
	eval_neg(&rd, opsz, msk);

	uint64_t wit;
#if defined(BMC_UMAX)
	wit = pre(rd.u.max, msk);
#elif defined(BMC_UMIN)
	wit = pre(rd.u.min, msk);
#elif defined(BMC_SMAX)
	wit = pre((uint64_t)rd.s.max & msk, msk);
#elif defined(BMC_SMIN)
	wit = pre((uint64_t)rd.s.min & msk, msk);
#else
# error "define a BMC_* endpoint (UMAX/UMIN/SMAX/SMIN)"
#endif

	assert(repr(&od, wit, msk));
	return 0;
}
