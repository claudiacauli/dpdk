
#include <assert.h>
#include "eval_neg.h"
#include "../eval_apply_mask/eval_apply_mask.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int ordering(const struct bpf_reg_val *rv)
{
	return rv->u.min <= rv->u.max && rv->s.min <= rv->s.max;
}
static int sign_determinate(const struct bpf_reg_val *rv, uint64_t m)
{
	return rv->s.min >= 0 || rv->s.max < 0 ||
		rv->u.min > (m >> 1) || rv->u.max <= (m >> 1);
}
static int min_agreement(const struct bpf_reg_val *rv, uint64_t m)
{
	return !sign_determinate(rv, m) ||
		rv->u.min == ((uint64_t)rv->s.min & m);
}
static int max_agreement(const struct bpf_reg_val *rv, uint64_t m)
{
	return !sign_determinate(rv, m) ||
		rv->u.max == ((uint64_t)rv->s.max & m);
}
static int within_width(const struct bpf_reg_val *rv, uint64_t m)
{
	return rv->u.max <= m &&
		-(int64_t)(m >> 1) - 1 <= rv->s.min &&
		rv->s.max <= (int64_t)(m >> 1);
}

static int P(const struct bpf_reg_val *rv, uint64_t m)
{
#if   CAND == 0
	return ordering(rv);
#elif CAND == 1
	return ordering(rv) && within_width(rv, m);
#elif CAND == 2
	return ordering(rv) && within_width(rv, m) && rv->s.min <= 0;
#elif CAND == 3
	return ordering(rv) && within_width(rv, m) && min_agreement(rv, m);
#elif CAND == 4
	return ordering(rv) && within_width(rv, m) && max_agreement(rv, m);
#elif CAND == 5

	return ordering(rv) && within_width(rv, m) &&
		((rv->u.min != 0) || (rv->s.min <= 0));
#elif CAND == 6
	return ordering(rv) && within_width(rv, m) &&
		min_agreement(rv, m) && max_agreement(rv, m);
#else
#error "define CAND"
#endif
}

int main(void)
{
	struct bpf_reg_val rd;
	uint64_t regmask, msk;
	size_t opsz;

	msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
	opsz = (msk == _32_BIT_MASK) ? 32 : 64;

	rd.v.type = RTE_BPF_ARG_RAW;
	rd.u.min = nondet_u64();
	rd.u.max = nondet_u64();
	rd.s.min = nondet_i64();
	rd.s.max = nondet_i64();

#ifdef MODE_ESTABLISH

	regmask = nondet_u64();
	REQUIRE(regmask == _32_BIT_MASK || regmask == _64_BIT_MASK);
	rd.mask = regmask;
	REQUIRE(ordering(&rd));
	REQUIRE(within_width(&rd, regmask));
	REQUIRE(min_agreement(&rd, regmask) && max_agreement(&rd, regmask));

	eval_apply_mask(&rd, msk);

	assert(P(&rd, msk));
#endif

#ifdef MODE_SUFFICE
	rd.mask = msk;
	REQUIRE(P(&rd, msk));

	eval_neg(&rd, opsz, msk);

	assert(rd.u.min <= rd.u.max);
	assert(rd.s.min <= rd.s.max);
#endif
	return 0;
}
