/*
 * BMC harness for eval_apply_mask (mirrors the ACSL contract in
 * eval_apply_mask.c). Loop-free, full-width symbolic inputs: complete.
 *
 * Run from this directory:
 *   cbmc  -DALL_FIXES eval_apply_mask_bmc.c eval_apply_mask.c \
 *         ../eval_smax_bound/eval_smax_bound.c
 *   esbmc -DALL_FIXES (same file list)
 */
#include <assert.h>
#include "eval_apply_mask.h"

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

#ifdef BMC_WIDEN_WITNESS
/*
 * CANDIDATE DEFECT #9 — deterministic reproduction of the widening
 * witness-transport failure. ESBMC-found 2026-07-30; see
 * docs/review_04_composition.md §4.1.
 *
 * A CHARACTERIZATION test: it asserts upstream's CURRENT (unsound)
 * behaviour, so it passes while the defect is present. If it ever
 * FAILS, eval_apply_mask's widening semantics changed — that is good
 * news, but re-read §4.1 and retire this leg rather than "fixing" it.
 *
 * All values are concrete, so this is a single-path check.
 */
/*
 * WITNESS A — the TOP 32-bit register. This is the canonical one: it is
 * what eval_max_bound emits for ANY unknown 32-bit result, so it is the
 * most trivially reachable state in the validator, not a contrived range.
 * The escaping value is 0x80000000 and the overshoot is exactly 1.
 */
static void widen_witness_top(void)
{
	struct bpf_reg_val rv;
	rv.v.type = RTE_BPF_ARG_RAW;
	rv.v.size = 0;
	rv.v.buf_size = 0;
	rv.mask  = _32_BIT_MASK;
	rv.u.min = 0;
	rv.u.max = _32_BIT_MASK;              /* TOP at 32 bits */
	rv.s.min = INT32_MIN;
	rv.s.max = INT32_MAX;

	const struct bpf_reg_val old = rv;
	const uint64_t wt = 0x80000000u;      /* the sign bit alone */

	assert(range_ordering(&old));
	assert(range_agreement(&old, old.mask));
	assert(old.u.max <= old.mask);
	assert(old.u.min <= wt && wt <= old.u.max);
	/* admitted at its own mask: 32-bit reading is INT32_MIN */
	assert((int64_t)wt - ((int64_t)old.mask + 1) == INT32_MIN);

	eval_apply_mask(&rv, _64_BIT_MASK);   /* a 64-bit op reads it */

	assert(rv.s.min == old.s.min && rv.s.max == old.s.max);
	/* true 64-bit reading is +2^31, one past the tracked maximum */
	assert(!(rv.s.min <= (int64_t)wt && (int64_t)wt <= rv.s.max));
	assert((int64_t)wt - rv.s.max == 1);
}

int main(void)
{
	widen_witness_top();

	/* WITNESS B — the range ESBMC found first, kept as a second data
	 * point: the failure is not special to TOP. */
	struct bpf_reg_val rv;
	rv.v.type = RTE_BPF_ARG_RAW;
	rv.v.size = 0;
	rv.v.buf_size = 0;
	rv.mask  = _32_BIT_MASK;              /* tracked at 32 bits */
	rv.u.min = 1075380245u;
	rv.u.max = 3222863894u;
	rv.s.min = -1072103403;
	rv.s.max = 1075380246;

	const struct bpf_reg_val old = rv;
	const uint64_t wt = 3222863893u;      /* 0xC0190015 */

	/* wt is a value this register genuinely admits, read at ITS OWN
	 * mask: pattern inside u, 32-bit signed reading inside s. */
	assert(wt <= old.mask);
	assert(old.u.min <= wt && wt <= old.u.max);
	const int64_t own_reading = (int64_t)wt - ((int64_t)old.mask + 1);
	assert(own_reading == -1072103403);   /* == old.s.min exactly */
	assert(old.s.min <= own_reading && own_reading <= old.s.max);

	/* the register is well-formed by the validator's own invariant
	 * (agreement holds — vacuously, the range straddles the sign
	 * boundary, so sign_determinate is false at 32 bits) */
	assert(range_ordering(&old));
	assert(range_agreement(&old, old.mask));
	assert(old.u.max <= old.mask);

	/* a 64-bit ALU op reads it: WIDENING */
	eval_apply_mask(&rv, _64_BIT_MASK);

	/* the signed track is carried over untouched ... */
	assert(rv.s.min == old.s.min && rv.s.max == old.s.max);
	/* ... but the value's TRUE 64-bit signed reading is its pattern, */
	const int64_t true_reading = (int64_t)wt;
	assert(true_reading == 3222863893);
	/* which the tracked signed range does NOT cover. The validator now
	 * believes this register is at most 1075380246 while it can hold
	 * 3222863893 — an overshoot of exactly 2^31 - 1. */
	assert(!(rv.s.min <= true_reading && true_reading <= rv.s.max));
	assert(true_reading - rv.s.max == 2147483647);
	return 0;
}
#else
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

	/* requires range_ordering(rv) */
	REQUIRE(rv.u.min <= rv.u.max && rv.s.min <= rv.s.max);

	/* \old(*rv) */
	const struct bpf_reg_val old = rv;

	/* concrete witnesses for the soundness \forall */
	uint64_t wx = nondet_u64();
	REQUIRE(old.u.min <= wx && wx <= old.u.max);
	int64_t wv = nondet_i64();
	REQUIRE(old.s.min <= wv && wv <= old.s.max);
	/* intersection witness (see eval_apply_mask.h): the value must also
	 * satisfy the unsigned track — its 64-bit pattern lies in old.u.
	 * FIX_APPLY_MASK_CONSIST derives s from u (a cross-track flow), so
	 * ssound is only claimed over the intersection. */
	REQUIRE(old.u.min <= (uint64_t)wv && (uint64_t)wv <= old.u.max);

#ifdef BMC_WSOUND
	/*
	 * Witness TRANSPORT (the wsound ensures): a value the register could
	 * hold — pattern within the unsigned track AND canonical reading AT
	 * THE REGISTER'S OWN MASK within the signed track — is, once masked
	 * to the op width, covered by both result tracks. Claimed only for
	 * well-formed register masks (the verifier loop invariant). This is
	 * the composition-ready witness shape: ssound's 64-bit-cast witness
	 * goes vacuous for narrower-tracked registers with negative
	 * readings, which is why eval_alu's soundness cannot chain through
	 * ssound alone.
	 */
	uint64_t wt = nondet_u64();
	REQUIRE(old.mask == _32_BIT_MASK || old.mask == _64_BIT_MASK);
	/* the register respects its own width — every producer ensures this
	 * (the verifier loop invariant); without it ESBMC refutes wsound on
	 * 32-bit-tracked registers carrying 64-bit-scale garbage ranges */
	REQUIRE(old.u.max <= old.mask);
	REQUIRE(-(int64_t)(old.mask >> 1) - 1 <= old.s.min &&
		old.s.max <= (int64_t)(old.mask >> 1));
	/* the verifier's own loop invariant on the register: valid AT ITS OWN
	 * MASK. Ordering and within-width are required above; this adds
	 * agreement, so any counterexample is a register the validator
	 * itself considers well-formed rather than a state it never builds. */
	REQUIRE(range_agreement(&old, old.mask));
	/*
	 * WIDTH_FITS — the op width must not EXCEED the tracked width.
	 * This is not a convenience: without it the property is FALSE, and
	 * ESBMC produces the witness recorded in docs/review_04_composition.md
	 * §4.1 (reproduce it with -DBMC_WIDEN_WITNESS below). eval_apply_mask
	 * does not re-derive the signed track across a width INCREASE, so a
	 * 32-bit-tracked register's own-mask signed reading and its true
	 * 64-bit reading disagree by 2^32 and the kept s track fails to
	 * cover the value. Verified boundary: FAILS without this line,
	 * SUCCEEDS with it.
	 */
	REQUIRE(mask <= old.mask);
	REQUIRE(wt <= old.mask);
	REQUIRE(old.u.min <= wt && wt <= old.u.max);
	int64_t wtc = (wt <= (old.mask >> 1)) ? (int64_t)wt
					      : (int64_t)(wt - (old.mask + 1));
	REQUIRE(old.s.min <= wtc && wtc <= old.s.max);
#endif

	eval_apply_mask(&rv, mask);

	assert(mask != _64_BIT_MASK ||
		rv.u.min == old.u.min);                         /* umin64 */
	assert(mask != _64_BIT_MASK ||
		rv.u.max == old.u.max);                         /* umax64 */
	/*
	 * uwiden32/ukeep32 in the QUOTIENT form of the contract of record:
	 * optimal masking widens iff the range STRADDLES a block boundary
	 * (the bounds' 2^32-quotients differ); a range lying wholly in one
	 * block keeps its tight masked form. See eval_apply_mask.c.
	 *
	 * These two assertions previously encoded the PRE-FIX_APPLY_MASK_OPT
	 * semantics ("either bound exceeds mask ==> widen to [0,mask]"),
	 * which ALL_FIXES code no longer does — so this harness had been
	 * failing at uwiden32 on every bmc_all.sh run, and since a violated
	 * property ENDS an ESBMC run, it silently masked every assertion
	 * below it (ssound, agree_min/max, and the whole BMC_WSOUND leg).
	 * Corrected 2026-07-30. The `&&` short-circuit is what keeps
	 * mask + 1 from dividing by zero at _64_BIT_MASK.
	 */
	assert(!(mask == _32_BIT_MASK &&
		old.u.min / (mask + 1) != old.u.max / (mask + 1)) ||
		(rv.u.min == 0 && rv.u.max == mask));           /* uwiden32 */
	assert(!(mask == _32_BIT_MASK &&
		old.u.min / (mask + 1) == old.u.max / (mask + 1)) ||
		(rv.u.min == (old.u.min & mask) &&
		 rv.u.max == (old.u.max & mask)));              /* ukeep32 */
	assert(rv.mask == mask);                                /* mask_set */
	assert(rv.mask == _32_BIT_MASK ||
		rv.mask == _64_BIT_MASK);                       /* mask_ok */
	int64_t sxu_min = (rv.u.min <= (mask >> 1)) ? (int64_t)rv.u.min
			: (int64_t)(rv.u.min - (mask + 1));
	int64_t sxu_max = (rv.u.max <= (mask >> 1)) ? (int64_t)rv.u.max
			: (int64_t)(rv.u.max - (mask + 1));
	assert(mask != _32_BIT_MASK ||
		rv.s.min == INT32_MIN || rv.s.min == old.s.min ||
		rv.s.min == sxu_min);                            /* smin32 */
	assert(mask != _32_BIT_MASK ||
		rv.s.max == INT32_MAX || rv.s.max == old.s.max ||
		rv.s.max == sxu_max);                            /* smax32 */
	assert(mask != _64_BIT_MASK ||
		rv.s.min == INT64_MIN || rv.s.min == old.s.min ||
		rv.s.min == sxu_min);                            /* smin64 */
	assert(mask != _64_BIT_MASK ||
		rv.s.max == INT64_MAX || rv.s.max == old.s.max ||
		rv.s.max == sxu_max);                            /* smax64 */
	assert(rv.v.type == old.v.type &&
		rv.v.size == old.v.size &&
		rv.v.buf_size == old.v.buf_size);               /* unchanged_v */
	assert(rv.u.min <= rv.u.max);                           /* uord */
	assert(rv.s.min <= rv.s.max);                           /* sord */
	assert(rv.u.max <= mask);                               /* uwidth */
	assert(-(int64_t)(mask >> 1) - 1 <= rv.s.min &&
		rv.s.max <= (int64_t)(mask >> 1));              /* swidth */

	/*
	 * agree_min/agree_max in the CONTRACT OF RECORD form: conditioned on
	 * the OLD register already agreeing and fitting AT THE OP MASK.
	 *
	 * This block previously asserted the unconditional form, which holds
	 * only under FIX_APPLY_MASK_CONSIST — and that gate is DEAD: it is
	 * defined in common/fixes.h and gated nowhere in any harness .c, so
	 * the repair does not exist in the code under any flag. The
	 * unconditional assertion was therefore false, and (being reached
	 * only after the stale uwiden32 above) had never been executed.
	 * Corrected 2026-07-30 to match eval_apply_mask.c's ensures.
	 */
	{
		int old_det = old.s.min >= 0 || old.s.max < 0 ||
			old.u.min > (mask >> 1) || old.u.max <= (mask >> 1);
		int old_agree = !old_det ||
			(old.u.min == ((uint64_t)old.s.min & mask) &&
			 old.u.max == ((uint64_t)old.s.max & mask));
		int old_width = old.u.max <= mask &&
			-(int64_t)(mask >> 1) - 1 <= old.s.min &&
			old.s.max <= (int64_t)(mask >> 1);
		int det = rv.s.min >= 0 || rv.s.max < 0 ||
			rv.u.min > (mask >> 1) || rv.u.max <= (mask >> 1);
		assert(!(old_agree && old_width) || !det || rv.u.min ==
			((uint64_t)rv.s.min & mask));           /* agree_min */
		assert(!(old_agree && old_width) || !det || rv.u.max ==
			((uint64_t)rv.s.max & mask));           /* agree_max */
	}
	uint64_t mx = wx & mask;
	assert(rv.u.min <= mx && mx <= rv.u.max);               /* usound */
	uint64_t sm = ((uint64_t)wv) & mask;
	int64_t sv = (sm <= (mask >> 1)) ? (int64_t)sm
					 : (int64_t)(sm - (mask + 1));
	assert(rv.s.min <= sv && sv <= rv.s.max);               /* ssound */

#ifdef BMC_WSOUND
	uint64_t wtm = wt & mask;
	assert(rv.u.min <= wtm && wtm <= rv.u.max);             /* wsound u */
	int64_t wts = (wtm <= (mask >> 1)) ? (int64_t)wtm
					   : (int64_t)(wtm - (mask + 1));
	assert(rv.s.min <= wts && wts <= rv.s.max);             /* wsound s */
#endif

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
#endif /* BMC_WIDEN_WITNESS */
