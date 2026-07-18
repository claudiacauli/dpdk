/*
 * Intersection-soundness BMC harness for eval_neg (unary), matching the
 * declared WP contract (eval_neg.h bin_witness form): precondition is
 * is_scalar + range_ORDERING + range_within_width (agreement DROPPED); the
 * witness is a pattern in the unsigned range whose signed reading lies in the
 * signed range. Confirms the intersection-form usound/ssound WP contracts are
 * TRUE (BMC).
 *   default SUCCESSFUL  => intersection soundness holds.
 *   default FAILED (CEX) => the contract is wrong.
 *   -DBMC_SANITY assert(0) must be VIOLATED => asserts reachable (non-vacuous).
 */
#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int is_scalar(enum rte_bpf_arg_type t)
{
	return t == RTE_BPF_ARG_RAW;
}
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
static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
}
static void havoc_reg(struct bpf_reg_val *rv)
{
	rv->v.type = (enum rte_bpf_arg_type)nondet_int();
	rv->v.size = nondet_u64();
	rv->v.buf_size = nondet_u64();
	rv->mask = nondet_u64();
	rv->s.min = nondet_i64();
	rv->s.max = nondet_i64();
	rv->u.min = nondet_u64();
	rv->u.max = nondet_u64();
}

int main(void)
{
	struct bpf_reg_val rd;
	havoc_reg(&rd);

	uint64_t msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
#ifdef BMC_32
	REQUIRE(msk == _32_BIT_MASK);
#endif
#ifdef BMC_64
	REQUIRE(msk == _64_BIT_MASK);
#endif
	size_t opsz = nondet_size_t();
	REQUIRE(msk != _32_BIT_MASK || opsz == 32);
	REQUIRE(msk != _64_BIT_MASK || opsz == 64);

	/* requires: is_scalar + range_ORDERING (agreement DROPPED) + within_width */
	REQUIRE(is_scalar(rd.v.type));
	REQUIRE(range_ordering(&rd));
	REQUIRE(range_within_width(&rd, msk));

	const struct bpf_reg_val od = rd;

	/* INTERSECTION witness: a pattern in BOTH tracks */
	uint64_t px = nondet_u64();
	REQUIRE(od.u.min <= px && px <= od.u.max);
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);

	eval_neg(&rd, opsz, msk);

	assert(range_ordering(&rd));                            /* ord */
	assert(range_within_width(&rd, msk));                  /* width */

	/* machine negation of the w-bit pattern: (0 - x) mod 2^64, masked to w
	 * bits (== neg_pat(x, msk); cross-checks the spec against the machine) */
	uint64_t ures = (0 - px) & msk;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound (isect) */

	int64_t s_val = tos(ures, msk);
	assert(rd.s.min <= s_val && s_val <= rd.s.max);        /* ssound (isect) */

#ifdef BMC_SANITY
	assert(0);   /* must FAIL: proves the asserts are reachable */
#endif
	return 0;
}
