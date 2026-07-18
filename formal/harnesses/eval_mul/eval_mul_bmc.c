/*
 * Intersection-soundness BMC harness for eval_mul, matching the declared WP
 * contract (common/specs.h bin_witness form): precondition is is_scalar +
 * range_ORDERING + range_within_width (agreement DROPPED); the soundness
 * witness is a pattern lying in the unsigned range AND whose signed reading
 * lies in the signed range. Confirms the intersection-form usound/ssound WP
 * contracts are TRUE (BMC) before investing in the WP proof.
 *   default check SUCCESSFUL  => intersection soundness holds.
 *   default check FAILED (CEX) => the contract is wrong.
 *   -DBMC_SANITY assert(0) must be VIOLATED => asserts are reachable (non-vacuous).
 */
#include <assert.h>
#include "eval_mul.h"

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
/* C mirror of the ACSL to_signed logic function */
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
	struct bpf_reg_val rd, rs;
	havoc_reg(&rd);
	havoc_reg(&rs);

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

	const struct bpf_reg_val *prs = &rs;

	/* requires: is_scalar + range_ORDERING (agreement DROPPED) + within_width */
	REQUIRE(is_scalar(rd.v.type));
	REQUIRE(is_scalar(prs->v.type));
	REQUIRE(range_ordering(&rd) && range_ordering(prs));
	REQUIRE(range_within_width(&rd, msk) && range_within_width(prs, msk));

	const struct bpf_reg_val od = rd, os = *prs;

	/* INTERSECTION witnesses: a pattern in BOTH tracks of each operand */
	uint64_t px = nondet_u64(), py = nondet_u64();
	REQUIRE(od.u.min <= px && px <= od.u.max);
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);
	REQUIRE(os.u.min <= py && py <= os.u.max);
	REQUIRE(os.s.min <= tos(py, msk) && tos(py, msk) <= os.s.max);

	eval_mul(&rd, prs, opsz, msk);

	assert(range_ordering(&rd));                            /* ord */
	assert(range_within_width(&rd, msk));                  /* width */

	/* intersection usound: ((x * y) & msk) covered by output u */
#ifndef BMC_S_ONLY
	uint64_t ures = (px * py) & msk;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound (isect) */
#endif

	/* intersection ssound: to_signed((v * w) & msk) covered by output s */
#ifndef BMC_U_ONLY
	uint64_t sres = (px * py) & msk;
	int64_t s_val = tos(sres, msk);
	assert(rd.s.min <= s_val && s_val <= rd.s.max);        /* ssound (isect) */
#endif

#ifdef BMC_SANITY
	assert(0);   /* must FAIL: proves the asserts are reachable */
#endif
	return 0;
}
