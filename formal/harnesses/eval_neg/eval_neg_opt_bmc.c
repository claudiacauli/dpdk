/*
 * OP-OPTIMALITY VERIFIER for eval_neg over FULLY NONDET input.
 *
 * Unlike eval_neg_tight_bmc.c (hand-picked regimes, existential-by-refutation),
 * this proves/refutes tightness for ALL valid non-empty inputs at once, as a
 * plain forall-safety property. The trick: neg_pat is a BIJECTION on [0, msk]
 * (0->0, and x->msk+1-x on [1,msk]), so each output endpoint M has a UNIQUE
 * preimage pre(M) = (M==0 ? 0 : msk+1-M). Hence
 *
 *     "endpoint M is attained"  <=>  pre(M) is representable in the input.
 *
 * For the signed endpoints t, the attaining pattern is pre(pattern(t)) with
 * pattern(t) = (uint64_t)t & msk (round-trips through to_signed).
 *
 * So the whole tightness question becomes a single assertion — no existential:
 *     VERIFICATION SUCCESSFUL => the endpoint is attained for EVERY valid
 *                                non-empty input (tight).
 *     VERIFICATION FAILED     => CEX input where the endpoint is NOT attained
 *                                (loose); the trace prints that input.
 *
 * Cell flags: -DBMC_UMAX|_UMIN|_SMAX|_SMIN, -DBMC_32|_64,
 *             -DBMC_NOAGREE drops range_agreement (stronger test),
 *             -DBMC_SANITY asserts(0) after the REQUIREs (must be VIOLATED).
 * Build with -DALL_FIXES -DFIX_NEG_ZERO.
 */
#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
}
/* is pattern x a value the register od can hold? (un_witness) */
static int repr(const struct bpf_reg_val *od, uint64_t x, uint64_t msk)
{
	return od->u.min <= x && x <= od->u.max &&
	       od->s.min <= tos(x, msk) && tos(x, msk) <= od->s.max;
}
/* unique preimage of M under neg_pat on [0, msk] */
static uint64_t pre(uint64_t m, uint64_t msk)
{
	return (m == 0) ? 0 : (msk + 1 - m);
}

int main(void)
{
	uint64_t msk;
	size_t opsz;
#ifdef BMC_32
	msk = _32_BIT_MASK; opsz = 32;
#else
	msk = _64_BIT_MASK; opsz = 64;
#endif

	struct bpf_reg_val rd;
	rd.v.type = RTE_BPF_ARG_RAW;
	rd.v.size = 0;
	rd.v.buf_size = 0;
	rd.mask = msk;
	rd.s.min = nondet_i64();
	rd.s.max = nondet_i64();
	rd.u.min = nondet_u64();
	rd.u.max = nondet_u64();

	/* valid scalar register: ordering + within_width */
	REQUIRE(rd.u.min <= rd.u.max);
	REQUIRE(rd.s.min <= rd.s.max);
	REQUIRE(rd.u.max <= msk);
	REQUIRE(-(int64_t)(msk >> 1) - 1 <= rd.s.min && rd.s.max <= (int64_t)(msk >> 1));

#ifndef BMC_NOAGREE
	/* range_agreement: when sign-determinate, the tracks must agree */
	int det = rd.s.min >= 0 || rd.s.max < 0 ||
	          rd.u.min > (msk >> 1) || rd.u.max <= (msk >> 1);
	if (det) {
		REQUIRE(rd.u.min == ((uint64_t)rd.s.min & msk));
		REQUIRE(rd.u.max == ((uint64_t)rd.s.max & msk));
	}
#endif

	/* INPUT SELF-OPTIMALITY (input self-optimality): each input range endpoint is itself
	 * attained by a representable value -- i.e. the ranges are the OPTIMAL
	 * abstraction of the value set, not a loose over-approximation of it. No
	 * operator can produce a tight output from a loose input, so tightness is
	 * a PRESERVATION property conditioned on this. (Subsumes non-emptiness.) */
	REQUIRE(repr(&rd, rd.u.min, msk));                    /* u.min attained */
	REQUIRE(repr(&rd, rd.u.max, msk));                    /* u.max attained */
	REQUIRE(repr(&rd, (uint64_t)rd.s.min & msk, msk));    /* s.min attained */
	REQUIRE(repr(&rd, (uint64_t)rd.s.max & msk, msk));    /* s.max attained */

#ifdef BMC_NOWRAP
	/* exclude inputs containing the width-minimum (INT_MIN), which negates to
	 * itself and breaks anti-monotonicity — isolates the wrap special-case */
	REQUIRE(rd.s.min != -(int64_t)(msk >> 1) - 1);
#endif

#ifdef BMC_SANITY
	assert(0);   /* must FAIL: the constrained input path is reachable */
#endif

	const struct bpf_reg_val od = rd;   /* original input */
	eval_neg(&rd, opsz, msk);           /* rd = nw */

	/* the unique pattern that would attain the selected output endpoint */
	uint64_t wit;
#if defined(BMC_UMAX)
	wit = pre(rd.u.max, msk);
#elif defined(BMC_UMIN)
	wit = pre(rd.u.min, msk);
#elif defined(BMC_SMAX)
	wit = pre((uint64_t)rd.s.max & msk, msk);
#elif defined(BMC_SMIN)
	wit = pre((uint64_t)rd.s.min & msk, msk);
#else
# error "define a BMC_* endpoint (UMAX/UMIN/SMAX/SMIN)"
#endif

	/* tight iff that unique preimage is a representable input value */
	assert(repr(&od, wit, msk));
	return 0;
}
