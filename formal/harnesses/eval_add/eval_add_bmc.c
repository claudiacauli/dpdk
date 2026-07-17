/*
 * BMC counterexample hunt for the eval_add soundness postconditions
 * (mirrors the ACSL contract in eval_add.c / eval_add.h).
 *
 * The code under test is loop-free and every input below is a fresh
 * full-width symbolic value constrained only by the mirrored requires
 * clauses, so the check is COMPLETE for the C semantics: a pass is a
 * proof over the whole input space, a failure comes with a concrete
 * counterexample trace.
 *
 * Run from this directory (CBMC):
 *
 *   cbmc -DALL_FIXES eval_add_bmc.c eval_add.c \
 *        ../eval_fill_max_bound/eval_fill_max_bound.c \
 *        ../eval_max_bound/eval_max_bound.c \
 *        ../eval_umax_bound/eval_umax_bound.c \
 *        ../eval_smax_bound/eval_smax_bound.c
 *
 * or (ESBMC):
 *
 *   esbmc -DALL_FIXES eval_add_bmc.c eval_add.c \
 *        ../eval_fill_max_bound/eval_fill_max_bound.c \
 *        ../eval_max_bound/eval_max_bound.c \
 *        ../eval_umax_bound/eval_umax_bound.c \
 *        ../eval_smax_bound/eval_smax_bound.c
 *
 * Add --trace (CBMC) to get counterexample values for a failing property.
 *
 * Vacuity guard: rebuild with -DBMC_SANITY and expect a FAILURE on the
 * final assert(0); if that assert is unreachable, the mirrored
 * preconditions are contradictory and every other pass is vacuous.
 */
#include <assert.h>
#include "eval_add.h"

/* Bodyless declarations: both CBMC and ESBMC return a fresh symbolic
 * value for them (ESBMC keys on the nondet_ prefix). */
uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

/* Portable assume: cutting the path is equivalent to __CPROVER_assume /
 * __ESBMC_assume for every assert that comes after it. */
#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/* ---- C mirrors of the ACSL predicates in common/specs.h ---- */

static int is_scalar_or_pointer(enum rte_bpf_arg_type t)
{
	return t == RTE_BPF_ARG_RAW || t == RTE_BPF_ARG_PTR ||
		t == RTE_BPF_ARG_PTR_MBUF || t == RTE_BPF_ARG_RESERVED;
}

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

	/* BPF allows `add rX, rX`: exercise the rd == rs alias case too.
	 * Deliberately WIDER than the WP contract (which requires
	 * \separated(rd, rs), matching eval_alu's fresh-local-copy caller):
	 * the aliased add still verifies, so BMC keeps the extra coverage. */
	const struct bpf_reg_val *prs = nondet_int() ? &rd : &rs;

	/* requires clauses of eval_add */
	REQUIRE(is_scalar_or_pointer(rd.v.type));
	REQUIRE(is_scalar_or_pointer(prs->v.type));
	REQUIRE(range_validity(&rd, msk) && range_validity(prs, msk));
	REQUIRE(range_within_width(&rd, msk) && range_within_width(prs, msk));

	/* \old(*rd), \old(*rs) */
	const struct bpf_reg_val od = rd, os = *prs;

	/* concrete witnesses for the \forall x, y of the two predicates */
	int64_t x = nondet_i64(), y = nondet_i64();
	REQUIRE(od.s.min <= x && x <= od.s.max);
	REQUIRE(os.s.min <= y && y <= os.s.max);

	uint64_t ux = nondet_u64(), uy = nondet_u64();
	REQUIRE(od.u.min <= ux && ux <= od.u.max);
	REQUIRE(os.u.min <= uy && uy <= os.u.max);

	eval_add(&rd, prs, msk);

	/* cross-check of the WP-proved postconditions */
	assert(is_scalar_or_pointer(rd.v.type));        /* type_ok */
	assert(range_ordering(&rd));                    /* ord     */
	assert(range_within_width(&rd, msk));           /* uwidth + swidth */

	/* usound: proved by WP, re-checked here as a harness sanity bar */
	uint64_t usum = (ux + uy) & msk;
	assert(rd.u.min <= usum && usum <= rd.u.max);   /* usound */

	/* ssound: mirrors to_signed(((uint64_t)x + (uint64_t)y) & msk, msk)
	 * from eval_add.h — the sign-extended (width-canonical) value of
	 * the masked sum. For msk == UINT64_MAX, msk + 1 wraps to 0 and
	 * the subtraction degenerates to the plain int64 cast, which is
	 * exactly to_signed's value there. */
	uint64_t ssum = ((uint64_t)x + (uint64_t)y) & msk;
	int64_t s_val = (ssum <= (msk >> 1)) ? (int64_t)ssum
					     : (int64_t)(ssum - (msk + 1));
	assert(rd.s.min <= s_val && s_val <= rd.s.max); /* ssound */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
