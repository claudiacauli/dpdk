#include <assert.h>
#include "eval_neg.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
size_t nondet_size_t(void);

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
	struct bpf_reg_val rd;

	havoc_reg(&rd);

	uint64_t msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
#ifdef BMC_32
	/* restrict to the 32-bit mask: cheap for the solver, and both
	 * signed-track defects (patterns stored un-extended; INT32_MIN wrap
	 * unguarded) manifest exactly here. */
	REQUIRE(msk == _32_BIT_MASK);
#endif
#ifdef BMC_64
	/* restrict to the 64-bit mask: isolates the claim that the upstream
	 * signed track is correct there. */
	REQUIRE(msk == _64_BIT_MASK);
#endif

	size_t opsz = nondet_size_t();
	REQUIRE(msk != _32_BIT_MASK || opsz == 32);
	REQUIRE(msk != _64_BIT_MASK || opsz == 64);

	/* requires clauses */
	REQUIRE(is_scalar_or_pointer(rd.v.type));
	REQUIRE(range_validity(&rd, msk));
	REQUIRE(range_within_width(&rd, msk));

	/* \old(*rd) */
	const struct bpf_reg_val od = rd;

	/* concrete witness: a register value satisfies BOTH tracks — its
	 * pattern lies in the unsigned range AND its canonical reading lies
	 * in the signed range (eval_neg exchanges information across tracks
	 * via cross_limits, so the intersection is the faithful witness
	 * set — see eval_neg.h) */
	uint64_t ux = nondet_u64();
	REQUIRE(od.u.min <= ux && ux <= od.u.max);
	int64_t xr = (ux <= (msk >> 1)) ? (int64_t)ux
					: (int64_t)(ux - (msk + 1));
	REQUIRE(od.s.min <= xr && xr <= od.s.max);

	eval_neg(&rd, opsz, msk);

	/* cross-check of the intended postconditions */
	assert(is_scalar_or_pointer(rd.v.type));        /* type_ok */
	assert(range_ordering(&rd));                    /* uord + sord */
	assert(range_within_width(&rd, msk));           /* uwidth + swidth */
	assert(rd.v.type == od.v.type &&
		rd.v.size == od.v.size &&
		rd.v.buf_size == od.v.buf_size);        /* unchanged_v */
	assert(rd.mask == od.mask);                     /* unchanged_mask */

	/* the REAL machine negation of the w-bit pattern (independent of the
	 * spec's linear neg_pat model — this is the cross-check that the
	 * model matches the machine: (0 - x) mod 2^64, masked to w bits) */
	uint64_t ures = (0 - ux) & msk;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound */

	/* signed view: canonical (sign-extended) value of the result */
	int64_t s_val = (ures <= (msk >> 1)) ? (int64_t)ures
					     : (int64_t)(ures - (msk + 1));
	assert(rd.s.min <= s_val && s_val <= rd.s.max);        /* ssound */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
