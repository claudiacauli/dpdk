
#include <assert.h>
#include "eval_neg.h"
#include "../eval_apply_mask/eval_apply_mask.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int range_ordering(const struct bpf_reg_val *rv)
{
	return rv->u.min <= rv->u.max && rv->s.min <= rv->s.max;
}

static int sign_determinate(const struct bpf_reg_val *rv, uint64_t mask)
{
	return rv->s.min >= 0 || rv->s.max < 0 ||
		rv->u.min > (mask >> 1) || rv->u.max <= (mask >> 1);
}

static int range_agreement(const struct bpf_reg_val *rv, uint64_t mask)
{
	if (sign_determinate(rv, mask))
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

int main(void)
{
	struct bpf_reg_val rd;
	uint64_t regmask, msk;
	size_t opsz;

	regmask = nondet_u64();
	REQUIRE(regmask == _32_BIT_MASK || regmask == _64_BIT_MASK);

	msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
	opsz = (msk == _32_BIT_MASK) ? 32 : 64;

	rd.v.type = RTE_BPF_ARG_RAW;
	rd.mask = regmask;
	rd.u.min = nondet_u64();
	rd.u.max = nondet_u64();
	rd.s.min = nondet_i64();
	rd.s.max = nondet_i64();

	REQUIRE(range_ordering(&rd));
	REQUIRE(range_within_width(&rd, regmask));
	REQUIRE(range_agreement(&rd, regmask));

	eval_apply_mask(&rd, msk);

	eval_neg(&rd, opsz, msk);

	assert(rd.u.min <= rd.u.max);
	assert(rd.s.min <= rd.s.max);

	return 0;
}
