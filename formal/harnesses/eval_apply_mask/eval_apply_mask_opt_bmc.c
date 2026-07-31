
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
	rv.u.min = 0x100000000ULL; rv.u.max = 0x100000005ULL;
	rv.s.min = 0x100000000LL;  rv.s.max = 0x100000005LL;
#else
# error "define a regime R_ID64|R_FIT32|R_STRADDLE"
#endif
	rv.mask = mask;

	const struct bpf_reg_val od = rv;
	eval_apply_mask(&rv, mask);

	uint64_t v = nondet_u64();
	REQUIRE(repr(&od, v, _64_BIT_MASK));

#ifdef BMC_SANITY
	assert(0);
#endif
	uint64_t res = v & mask;
	assert(res <= rv.u.max);
	assert(res != rv.u.max);
	return 0;
}
