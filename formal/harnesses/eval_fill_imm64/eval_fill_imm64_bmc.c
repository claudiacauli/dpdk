#include <assert.h>
#include "eval_fill_imm64.h"

uint64_t nondet_u64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int range_ordering(const struct bpf_reg_val *rv)
{
	return rv->u.min <= rv->u.max && rv->s.min <= rv->s.max;
}

static int range_within_width(const struct bpf_reg_val *rv, uint64_t mask)
{
	return rv->u.max <= mask &&
		-(int64_t)(mask >> 1) - 1 <= rv->s.min &&
		rv->s.max <= (int64_t)(mask >> 1);
}

static void havoc_reg(struct bpf_reg_val *rv)
{
	rv->v.type = (enum rte_bpf_arg_type)nondet_int();
	rv->v.size = nondet_u64();
	rv->v.buf_size = nondet_u64();
	rv->mask = nondet_u64();
	rv->s.min = nondet_u64();
	rv->s.max = nondet_u64();
	rv->u.min = nondet_u64();
	rv->u.max = nondet_u64();
}

int main(void)
{
	struct bpf_reg_val rv;

	havoc_reg(&rv);

	uint64_t msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
#ifdef BMC_32

	REQUIRE(msk == _32_BIT_MASK);
#endif
#ifdef BMC_64
	REQUIRE(msk == _64_BIT_MASK);
#endif

	uint64_t val = nondet_u64();
	REQUIRE(val <= msk);

	eval_fill_imm64(&rv, msk, val);

	assert(rv.mask == msk);
	assert(range_ordering(&rv));
	assert(range_within_width(&rv, msk));

	assert(rv.u.min == val && rv.u.max == val);

	int64_t canon = (val <= (msk >> 1)) ? (int64_t)val
					    : (int64_t)(val - (msk + 1));
	assert(rv.s.min == canon && rv.s.max == canon);

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
