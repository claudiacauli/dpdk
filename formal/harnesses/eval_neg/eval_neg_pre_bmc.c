/*
 * PRECONDITION SEARCH for eval_neg.
 *
 * eval_neg currently requires range_validity (= ordering + agreement). That is
 * too strong: it forces eval_alu to carry the `vld_d` stone, which is FALSE at
 * the call site because eval_apply_mask does not re-establish agreement across
 * a width change. But plain range_ordering is too weak -- eval_neg's two
 * cross-track clamps pull from opposite directions and can inverX the interval
 * (u=[0,10], s=[-3,-1] -> s=[1,0]).
 *
 * So: find a predicate P strictly between them such that
 *
 *   ESTABLISH:  regs_ok(regmask) && apply_mask(msk)  ==>  P(msk)
 *   SUFFICE:    P(msk) && eval_neg(msk)              ==>  uord && sord
 *
 * Compile with -DCAND=<n> to select the candidate, and exactly one of
 * -DMODE_ESTABLISH / -DMODE_SUFFICE.
 *
 * VERDICT: VERIFICATION SUCCESSFUL = the implication holds.
 *          VERIFICATION FAILED     = counterexample, candidate rejected.
 * A candidate is USABLE only if BOTH modes come back SUCCESSFUL.
 */
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

/* ---- candidate predicates, weakest first ---- */
static int P(const struct bpf_reg_val *rv, uint64_t m)
{
#if   CAND == 0		/* range_ordering only (expected: too weak) */
	return ordering(rv);
#elif CAND == 1		/* + within_width at the OP mask */
	return ordering(rv) && within_width(rv, m);
#elif CAND == 2		/* + the signed track cannot start above zero */
	return ordering(rv) && within_width(rv, m) && rv->s.min <= 0;
#elif CAND == 3		/* + min_agreement only */
	return ordering(rv) && within_width(rv, m) && min_agreement(rv, m);
#elif CAND == 4		/* + max_agreement only */
	return ordering(rv) && within_width(rv, m) && max_agreement(rv, m);
#elif CAND == 5		/* the CROSS-TRACK COMPATIBILITY the clamps actually
			 * need: the unsigned range's negation cannot fall
			 * entirely outside the signed range */
	return ordering(rv) && within_width(rv, m) &&
		((rv->u.min != 0) || (rv->s.min <= 0));
#elif CAND == 6		/* full validity + width (the status quo) */
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
	/* Does apply_mask hand eval_neg a register satisfying P at msk,
	 * starting from eval_alu's regs_ok at the register's OWN mask? */
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
	/* Given P, does eval_neg keep both intervals non-empty? */
	rd.mask = msk;
	REQUIRE(P(&rd, msk));

	eval_neg(&rd, opsz, msk);

	assert(rd.u.min <= rd.u.max);	/* uord */
	assert(rd.s.min <= rd.s.max);	/* sord */
#endif
	return 0;
}
