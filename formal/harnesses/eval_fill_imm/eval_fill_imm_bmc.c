#include <assert.h>
#include "eval_fill_imm.h"

uint64_t nondet_u64(void);
int32_t nondet_i32(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int range_ordering(const struct bpf_reg_val *rv)
{
	return rv->u.min <= rv->u.max && rv->s.min <= rv->s.max;
}

static int range_agreement(const struct bpf_reg_val *rv,
	uint64_t mask)
{
	if (rv->s.min >= 0 || rv->s.max < 0 ||
			rv->u.min > (mask >> 1) || rv->u.max <= (mask >> 1))
		return rv->u.min == ((uint64_t)rv->s.min & mask) &&
			rv->u.max == ((uint64_t)rv->s.max & mask);
	return 1;
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

	int32_t imm = nondet_i32();

	eval_fill_imm(&rv, msk, imm);

	assert(rv.v.type == RTE_BPF_ARG_RAW);
	assert(rv.mask == msk);
	assert(range_ordering(&rv));
	assert(range_within_width(&rv, msk));
	assert(range_agreement(&rv, msk));

	uint64_t pat = (uint64_t)imm & msk;
	assert(rv.u.min == pat && rv.u.max == pat);

	int64_t canon = (pat <= (msk >> 1)) ? (int64_t)pat
					    : (int64_t)(pat - (msk + 1));
	assert(rv.s.min == canon && rv.s.max == canon);

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
