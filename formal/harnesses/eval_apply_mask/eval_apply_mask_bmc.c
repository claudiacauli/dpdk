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
	assert(!(mask == _32_BIT_MASK &&
		(old.u.min > mask || old.u.max > mask)) ||
		(rv.u.min == 0 && rv.u.max == mask));           /* uwiden32 */
	assert(!(mask == _32_BIT_MASK &&
		old.u.min <= mask && old.u.max <= mask) ||
		(rv.u.min == old.u.min && rv.u.max == old.u.max)); /* ukeep32 */
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
	 * UNCONDITIONAL under FIX_APPLY_MASK_CONSIST: the repair makes the
	 * masked register sign-consistent from range_ordering alone (the
	 * old conditional form documented upstream's gap: a 64-bit-tracked
	 * register masked to 32 lost the guarantee).
	 */
	{
		int det = rv.s.min >= 0 || rv.s.max < 0 ||
			rv.u.min > (mask >> 1) || rv.u.max <= (mask >> 1);
		assert(!det || rv.u.min ==
			((uint64_t)rv.s.min & mask));           /* agree_min */
		assert(!det || rv.u.max ==
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
