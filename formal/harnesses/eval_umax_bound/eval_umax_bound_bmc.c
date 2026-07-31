
#include <assert.h>
#include "eval_umax_bound.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

int main(void)
{
	struct bpf_reg_val rv;

	rv.v.type = (enum rte_bpf_arg_type)nondet_int();
	rv.v.size = nondet_u64();
	rv.v.buf_size = nondet_u64();
	rv.mask = nondet_u64();
	rv.s.min = nondet_i64();
	rv.s.max = nondet_i64();
	rv.u.min = nondet_u64();
	rv.u.max = nondet_u64();

	uint64_t mask = nondet_u64();
	REQUIRE(mask == _32_BIT_MASK || mask == _64_BIT_MASK);

	const struct bpf_reg_val old = rv;

	eval_umax_bound(&rv, mask);

	assert(rv.u.min == 0 && rv.u.max == mask);
	assert(rv.u.max == _32_BIT_MASK ||
		rv.u.max == _64_BIT_MASK);
	assert(rv.s.min == old.s.min &&
		rv.s.max == old.s.max);
	assert(rv.mask == old.mask);
	assert(rv.v.type == old.v.type &&
		rv.v.size == old.v.size &&
		rv.v.buf_size == old.v.buf_size);
	assert(rv.u.min <= rv.u.max);
	assert(rv.u.max <= mask);

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
