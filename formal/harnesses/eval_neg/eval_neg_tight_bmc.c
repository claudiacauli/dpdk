
#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
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
#if defined(BMC_REG_POS)
	rd.u.min = 3;        rd.u.max = 10;
	rd.s.min = 3;        rd.s.max = 10;
#elif defined(BMC_REG_NEG)
	rd.u.min = msk - 9;  rd.u.max = msk - 2;
	rd.s.min = -10;      rd.s.max = -3;
#elif defined(BMC_REG_INCL0_RESTR)

	rd.u.min = 0;        rd.u.max = msk;
	rd.s.min = -5;       rd.s.max = 0;
#elif defined(BMC_REG_INCL0_TRUNC)

	rd.u.min = 0;        rd.u.max = (msk >> 1) + 1;
	rd.s.min = -1;       rd.s.max = 0;
#elif defined(BMC_REG_INCL0_PERM)

	rd.u.min = 0;        rd.u.max = msk;
	rd.s.min = -5;       rd.s.max = 5;
#else
# error "define a BMC_REG_* regime"
#endif

	REQUIRE(rd.u.min <= rd.u.max);
	REQUIRE(rd.s.min <= rd.s.max);
	REQUIRE(rd.u.max <= msk);
	REQUIRE(-(int64_t)(msk >> 1) - 1 <= rd.s.min && rd.s.max <= (int64_t)(msk >> 1));

	const struct bpf_reg_val od = rd;
	eval_neg(&rd, opsz, msk);

	uint64_t px = nondet_u64();
	REQUIRE(px <= msk);

#if defined(BMC_TRACK)
  #if defined(BMC_UMAX) || defined(BMC_UMIN)
	REQUIRE(od.u.min <= px && px <= od.u.max);
  #else
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);
  #endif
#else
	REQUIRE(od.u.min <= px && px <= od.u.max);
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);
#endif

#ifdef BMC_SANITY
	assert(0);
#endif

	uint64_t uval = (0 - px) & msk;
	int64_t  sval = tos(uval, msk);

#if defined(BMC_UMAX)
	assert(uval != rd.u.max);
#elif defined(BMC_UMIN)
	assert(uval != rd.u.min);
#elif defined(BMC_SMAX)
	assert(sval != rd.s.max);
#elif defined(BMC_SMIN)
	assert(sval != rd.s.min);
#else
# error "define a BMC_* endpoint (UMAX/UMIN/SMAX/SMIN)"
#endif
	return 0;
}
