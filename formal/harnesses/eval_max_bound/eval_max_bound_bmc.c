/*
 * BMC harness for eval_max_bound (mirrors the ACSL contract in
 * eval_max_bound.c). Loop-free, full-width symbolic inputs: complete.
 *
 * Run from this directory:
 *   cbmc  -DALL_FIXES eval_max_bound_bmc.c eval_max_bound.c \
 *         ../eval_umax_bound/eval_umax_bound.c ../eval_smax_bound/eval_smax_bound.c
 *   esbmc -DALL_FIXES (same file list)
 */
#include <assert.h>
#include "eval_max_bound.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/* ---- C mirrors of the ACSL predicates in common/specs.h ---- */

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

static int range_validity(const struct bpf_reg_val *rv, uint64_t mask)
{
	return rv->v.type == RTE_BPF_ARG_UNDEF ||
		(range_ordering(rv) && range_agreement(rv, mask));
}

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

	/* \old(*rv) */
	const struct bpf_reg_val old = rv;

	eval_max_bound(&rv, mask);

	assert(rv.u.min == 0 && rv.u.max == mask);              /* ufull */
	assert(rv.u.max == _32_BIT_MASK ||
		rv.u.max == _64_BIT_MASK);                      /* umax_ok */
	assert(mask != _32_BIT_MASK ||
		(rv.s.min == INT32_MIN && rv.s.max == INT32_MAX)); /* sfull32 */
	assert(mask != _64_BIT_MASK ||
		(rv.s.min == INT64_MIN && rv.s.max == INT64_MAX)); /* sfull64 */
	assert(rv.mask == old.mask);                            /* unchanged_mask */
	assert(rv.v.type == old.v.type &&
		rv.v.size == old.v.size &&
		rv.v.buf_size == old.v.buf_size);               /* unchanged_v */
	assert(rv.u.min <= rv.u.max);                           /* uord */
	assert(rv.s.min <= rv.s.max);                           /* sord */
	assert(range_validity(&rv, mask));                      /* valid */
	assert(rv.u.max <= mask);                               /* uwidth */
	assert(-(int64_t)(mask >> 1) - 1 <= rv.s.min &&
		rv.s.max <= (int64_t)(mask >> 1));              /* swidth */

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
