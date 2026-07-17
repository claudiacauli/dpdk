/*
 * BMC harness for eval_smax_bound (mirrors the ACSL contract in
 * eval_smax_bound.c). Loop-free, full-width symbolic inputs: complete.
 *
 * Run from this directory:
 *   cbmc  -DALL_FIXES eval_smax_bound_bmc.c eval_smax_bound.c
 *   esbmc -DALL_FIXES eval_smax_bound_bmc.c eval_smax_bound.c
 */
#include <assert.h>
#include "eval_smax_bound.h"

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

	/* \old(*rv) */
	const struct bpf_reg_val old = rv;

	eval_smax_bound(&rv, mask);

	assert(mask != _32_BIT_MASK ||
		(rv.s.min == INT32_MIN && rv.s.max == INT32_MAX)); /* sfull32 */
	assert(mask != _64_BIT_MASK ||
		(rv.s.min == INT64_MIN && rv.s.max == INT64_MAX)); /* sfull64 */
	assert(rv.u.min == old.u.min &&
		rv.u.max == old.u.max);                         /* unchanged_u */
	assert(rv.mask == old.mask);                            /* unchanged_mask */
	assert(rv.v.type == old.v.type &&
		rv.v.size == old.v.size &&
		rv.v.buf_size == old.v.buf_size);               /* unchanged_v */
	assert(rv.s.min <= rv.s.max);                           /* sord */
	assert(-(int64_t)(mask >> 1) - 1 <= rv.s.min &&
		rv.s.max <= (int64_t)(mask >> 1));              /* swidth */

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
