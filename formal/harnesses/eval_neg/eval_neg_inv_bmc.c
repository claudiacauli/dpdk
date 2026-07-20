/*
 * BMC harness: can the COMPOSITION eval_apply_mask -> eval_neg produce an
 * INVERTED interval (s.min > s.max or u.min > u.max)?
 *
 * WHY THIS EXISTS. eval_neg ends with two cross-track clamps that pull from
 * OPPOSITE directions, using limits derived from the other track:
 *
 *     rd->s.min = RTE_MAX(rd->s.min, cross_limits.s.min) & msk;
 *     rd->s.max = RTE_MIN(rd->s.max, cross_limits.s.max) & msk;
 *
 * If the two tracks disagree, the clamps cross and the interval inverts.
 * An inverted interval denotes the EMPTY set, so every downstream range
 * check on that register becomes vacuously true -- a soundness hazard.
 *
 * Hand-tracing upstream (no FIX_ gates) already shows eval_neg alone
 * inverts on u=[0,10], s=[-3,-1]. What that does NOT establish is whether
 * such a disagreeing register is REACHABLE. This harness closes that gap by
 * driving eval_neg only with states eval_apply_mask can actually PRODUCE,
 * starting from the register-file invariant eval_alu assumes (regs_ok):
 * ordered, in-width, and agreeing AT THE REGISTER'S OWN MASK -- which is a
 * different mask from the instruction's.
 *
 * That mask CHANGE is the suspected culprit: a 32-bit ALU op leaves
 * rd->mask = 2^32-1, and a following 64-bit op runs apply_mask at 2^64-1.
 *
 * Run from this directory:
 *   esbmc eval_neg_inv_bmc.c eval_neg.c ../eval_apply_mask/eval_apply_mask.c \
 *         ../eval_smax_bound/eval_smax_bound.c ../eval_umax_bound/eval_umax_bound.c \
 *         ../eval_max_bound/eval_max_bound.c
 * (add -DALL_FIXES to check whether the fixed build closes the hole)
 *
 * VERDICT READING: a counterexample means the inversion is REACHABLE and
 * this is a genuine upstream defect. "No property violation" means the
 * composition is safe and the hand-picked tuples are unreachable states.
 */
#include <assert.h>
#include "eval_neg.h"
#include "../eval_apply_mask/eval_apply_mask.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/* ---- C mirrors of the ACSL predicates in common/specs.h ---- */

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

	/* the register's OWN tracked width (set by whatever instruction
	 * last wrote it) */
	regmask = nondet_u64();
	REQUIRE(regmask == _32_BIT_MASK || regmask == _64_BIT_MASK);

	/* the CURRENT instruction's operand width -- deliberately
	 * independent: a 32-bit op may be followed by a 64-bit one */
	msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
	opsz = (msk == _32_BIT_MASK) ? 32 : 64;

	rd.v.type = RTE_BPF_ARG_RAW;
	rd.mask = regmask;
	rd.u.min = nondet_u64();
	rd.u.max = nondet_u64();
	rd.s.min = nondet_i64();
	rd.s.max = nondet_i64();

	/* exactly eval_alu's regs_ok: well-formed AT THE REGISTER'S OWN MASK.
	 * NOT at the instruction's msk -- that is the whole point. */
	REQUIRE(range_ordering(&rd));
	REQUIRE(range_within_width(&rd, regmask));
	REQUIRE(range_agreement(&rd, regmask));

	/* eval_alu narrows the destination to the instruction width first */
	eval_apply_mask(&rd, msk);

	/* ...then dispatches. BPF_NEG is the cross-track operator. */
	eval_neg(&rd, opsz, msk);

	/* THE CLAIM UNDER TEST: the result is a non-empty interval. */
	assert(rd.u.min <= rd.u.max);   /* uord */
	assert(rd.s.min <= rd.s.max);   /* sord */

	return 0;
}
