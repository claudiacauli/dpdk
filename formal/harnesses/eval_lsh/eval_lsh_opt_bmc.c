
#include <assert.h>
#include "eval_lsh.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
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
static int valid(const struct bpf_reg_val *o, uint64_t msk)
{
	return o->v.type == RTE_BPF_ARG_RAW &&
	       o->u.min <= o->u.max && o->s.min <= o->s.max &&
	       o->u.max <= msk &&
	       -(int64_t)(msk >> 1) - 1 <= o->s.min && o->s.max <= (int64_t)(msk >> 1);
}
static int self_optimal(const struct bpf_reg_val *o, uint64_t msk)
{
	return repr(o, o->u.min, msk) && repr(o, o->u.max, msk) &&
	       repr(o, (uint64_t)o->s.min & msk, msk) && repr(o, (uint64_t)o->s.max & msk, msk);
}
static void havoc(struct bpf_reg_val *o)
{
	o->v.type = RTE_BPF_ARG_RAW; o->v.size = 0; o->v.buf_size = 0; o->mask = 0;
	o->s.min = nondet_i64(); o->s.max = nondet_i64();
	o->u.min = nondet_u64(); o->u.max = nondet_u64();
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
	havoc(&rd); havoc(&rs);
	rd.mask = rs.mask = msk;
	REQUIRE(valid(&rd, msk) && valid(&rs, msk));
#ifndef BMC_NOSELFOPT
	REQUIRE(self_optimal(&rd, msk) && self_optimal(&rs, msk));
#else
	{ uint64_t wa = nondet_u64(), wb = nondet_u64();
	  REQUIRE(wa <= msk && repr(&rd, wa, msk));
	  REQUIRE(wb <= msk && repr(&rs, wb, msk)); }
#endif

	REQUIRE(rs.u.max < opsz);
	REQUIRE(rd.u.max <= (msk >> rs.u.max));
#if defined(BMC_SMAX) || defined(BMC_SMIN)
	REQUIRE(rd.s.min >= 0);
	{ uint64_t thr = (rs.u.max == opsz - 1) ? 0 : (msk >> (rs.u.max + 1));
	  REQUIRE((uint64_t)rd.s.max < thr); }
#endif

	uint64_t xv, sh;
#if defined(BMC_UMAX)
	xv = rd.u.max; sh = rs.u.max;
#elif defined(BMC_UMIN)
	xv = rd.u.min; sh = rs.u.min;
#elif defined(BMC_SMAX)
	xv = (uint64_t)rd.s.max & msk; sh = rs.u.max;
#elif defined(BMC_SMIN)
	xv = (uint64_t)rd.s.min & msk; sh = rs.u.min;
#else
# error "define a BMC_* endpoint"
#endif

#ifdef BMC_SANITY
	assert(0);
#endif
	const struct bpf_reg_val od = rd, os = rs;
	eval_lsh(&rd, &rs, opsz, msk);

	uint64_t res = (xv << sh) & msk;
	assert(repr(&od, xv, msk) && repr(&os, sh, msk));
#if defined(BMC_UMAX)
	assert(res == rd.u.max);
#elif defined(BMC_UMIN)
	assert(res == rd.u.min);
#elif defined(BMC_SMAX)
	assert(tos(res, msk) == rd.s.max);
#elif defined(BMC_SMIN)
	assert(tos(res, msk) == rd.s.min);
#endif
	return 0;
}
