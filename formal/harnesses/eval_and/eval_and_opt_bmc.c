
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

	const struct bpf_reg_val od = rd, os = rs;
	eval_and(&rd, &rs, opsz, msk);

	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(repr(&od, a, msk) && repr(&os, b, msk));

#ifdef BMC_SANITY
	assert(0);
#endif
	assert((a & b) <= rd.u.max);
	assert((a & b) != rd.u.max);
	return 0;
}
