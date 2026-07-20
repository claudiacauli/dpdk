/*
 * TIGHTNESS discovery harness for eval_neg (unary).
 *
 * Soundness says the computed range CONTAINS every result. Tightness is the
 * dual: each computed endpoint is ATTAINED by the image, i.e. some concrete
 * input negates to exactly that endpoint. The two notions differ only in the
 * WITNESS DOMAIN the endpoint must be attained from:
 *
 *   intersection (default): a real value the register can hold -- a pattern in
 *       the u-range whose signed reading is ALSO in the s-range (un_witness).
 *   per-track  (-DBMC_TRACK): the decoupled transformer -- a u-endpoint need
 *       only be attained by a pattern in the u-range (signed reading ignored);
 *       an s-endpoint only by a pattern whose reading is in the s-range.
 *
 * Since the intersection witness set is a SUBSET of each single-track set,
 * intersection tightness ==> per-track tightness. So per endpoint the verdict
 * is 3-valued: BOTH (intersection tight) / PER-TRACK-ONLY / NEITHER.
 *
 * ENCODING (existential via refutation): fix a concrete input regime, run
 * eval_neg, then feed a NONDET witness px constrained to the chosen domain and
 * assert it does NOT hit the endpoint. ESBMC then:
 *   VERIFICATION FAILED (CEX)  => it found a witness  => endpoint ATTAINED (tight)
 *   VERIFICATION SUCCESSFUL    => no witness exists    => endpoint LOOSE
 * The CEX trace prints the witnessing pattern -- exactly the term WP will need
 * to discharge the \exists.
 *
 * Cell flags:
 *   regime  : -DBMC_REG_POS | _NEG | _INCL0_RESTR | _INCL0_PERM  (concrete od)
 *   endpoint: -DBMC_UMAX | _UMIN | _SMAX | _SMIN
 *   notion  : default intersection; -DBMC_TRACK for per-track
 *   width   : default 64-bit; -DBMC_32 for 32-bit (exercises the sign-ext path)
 *   -DBMC_SANITY: assert(0) right after the domain REQUIREs -- must be VIOLATED,
 *                 proving the constrained witness path is reachable (non-vacuous,
 *                 so a SUCCESSFUL "loose" verdict is real and not empty-domain).
 *
 * Build with -DALL_FIXES (the contract we intend to prove is the fixed one).
 */
#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/* canonical w-bit reading, == to_signed(v, mask) */
static int64_t tos(uint64_t v, uint64_t mask)
{
	return (v <= (mask >> 1)) ? (int64_t)v : (int64_t)(v - (mask + 1));
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

	/* ---- concrete input regime (od) ---------------------------------- */
	struct bpf_reg_val rd;
	rd.v.type = RTE_BPF_ARG_RAW;
	rd.v.size = 0;
	rd.v.buf_size = 0;
	rd.mask = msk;
#if defined(BMC_REG_POS)
	/* all-positive box, exact corners -- expect BOTH everywhere */
	rd.u.min = 3;        rd.u.max = 10;
	rd.s.min = 3;        rd.s.max = 10;
#elif defined(BMC_REG_NEG)
	/* all-negative box (patterns near msk, readings -10..-3) */
	rd.u.min = msk - 9;  rd.u.max = msk - 2;
	rd.s.min = -10;      rd.s.max = -3;
#elif defined(BMC_REG_INCL0_RESTR)
	/* includes 0, RESTRICTIVE signed range that EXCLUDES 1:
	 * representable = {0} U [msk-4, msk] (readings 0, -1..-5).
	 * eval_neg widens u.max to msk; the true intersection u-image tops at 5.
	 * -> predict u.max PER-TRACK-ONLY, the rest BOTH. */
	rd.u.min = 0;        rd.u.max = msk;
	rd.s.min = -5;       rd.s.max = 0;
#elif defined(BMC_REG_INCL0_TRUNC)
	/* includes 0, s.max<=0, but u.max is BELOW the pattern of the most-negative
	 * reading s.min: the negatives are TRUNCATED out of the u-range, so the
	 * only representable value is 0 and the true image is {0}. The TIGHTEN fix
	 * (u.max = -s.min) OVERSHOOTS here -> exposes that the fix is incomplete. */
	rd.u.min = 0;        rd.u.max = (msk >> 1) + 1;   /* 2^(w-1): only the s.min pattern would fit, and its reading is out of s-range */
	rd.s.min = -1;       rd.s.max = 0;
#elif defined(BMC_REG_INCL0_PERM)
	/* includes 0, PERMISSIVE signed range that INCLUDES 1 (reading of x=1):
	 * now x=1 (which negates to the all-ones pattern msk) is representable,
	 * so u.max=msk is attained by a real value -> predict BOTH. */
	rd.u.min = 0;        rd.u.max = msk;
	rd.s.min = -5;       rd.s.max = 5;
#else
# error "define a BMC_REG_* regime"
#endif

	/* input must be a valid scalar register for the contract to apply */
	REQUIRE(rd.u.min <= rd.u.max);
	REQUIRE(rd.s.min <= rd.s.max);
	REQUIRE(rd.u.max <= msk);
	REQUIRE(-(int64_t)(msk >> 1) - 1 <= rd.s.min && rd.s.max <= (int64_t)(msk >> 1));

	const struct bpf_reg_val od = rd;
	eval_neg(&rd, opsz, msk);          /* rd is now the computed output nw */

	/* ---- nondet witness pattern, constrained by the chosen notion ---- */
	uint64_t px = nondet_u64();
	REQUIRE(px <= msk);                /* px is a valid w-bit pattern */

#if defined(BMC_TRACK)
  #if defined(BMC_UMAX) || defined(BMC_UMIN)
	/* per-track u-endpoint: constrain px by the u-range only */
	REQUIRE(od.u.min <= px && px <= od.u.max);
  #else
	/* per-track s-endpoint: constrain px by the s-range only */
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);
  #endif
#else
	/* intersection: px must be a real value -- in BOTH tracks */
	REQUIRE(od.u.min <= px && px <= od.u.max);
	REQUIRE(od.s.min <= tos(px, msk) && tos(px, msk) <= od.s.max);
#endif

#ifdef BMC_SANITY
	assert(0);   /* must FAIL: the constrained witness path is reachable */
#endif

	uint64_t uval = (0 - px) & msk;    /* machine neg pattern == neg_pat(px, msk) */
	int64_t  sval = tos(uval, msk);

	/* ---- refutation: assert the endpoint is NOT hit ------------------ */
#if defined(BMC_UMAX)
	assert(uval != rd.u.max);
#elif defined(BMC_UMIN)
	assert(uval != rd.u.min);
#elif defined(BMC_SMAX)
	assert(sval != rd.s.max);
#elif defined(BMC_SMIN)
	assert(sval != rd.s.min);
#else
# error "define a BMC_* endpoint (UMAX/UMIN/SMAX/SMIN)"
#endif
	return 0;
}
