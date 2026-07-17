#include <assert.h>
#include "eval_divmod.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
uint32_t nondet_u32(void);

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
#ifdef BMC_32
	/* restrict to the 32-bit mask: cheap for the bit-vector solver, and
	 * S1 (raw patterns stored as 32-bit signed bounds) manifests here. */
	REQUIRE(msk == _32_BIT_MASK);
#endif
#ifdef BMC_64
	/* restrict to the 64-bit mask: isolates the claim that the upstream
	 * signed reinterpretation is correct there (S1 is 32-bit-only). */
	REQUIRE(msk == _64_BIT_MASK);
#endif

	uint32_t op = nondet_u32();
	REQUIRE(op == BPF_DIV || op == BPF_MOD);
#ifdef BMC_DIV_ONLY
	REQUIRE(op == BPF_DIV);
#endif
#ifdef BMC_MOD_ONLY
	REQUIRE(op == BPF_MOD);
#endif

	/* eval_alu always hands eval_divmod a fresh local copy of the source
	 * register, and the WP contract requires \separated(rd, rs) */
	struct bpf_reg_val *prs = &rs;

	/* requires clauses */
	REQUIRE(is_scalar_or_pointer(rd.v.type));
	REQUIRE(is_scalar_or_pointer(prs->v.type));
	REQUIRE(range_validity(&rd, msk) && range_validity(prs, msk));
	REQUIRE(range_within_width(&rd, msk) && range_within_width(prs, msk));

	/* \old(*rd), \old(*rs) */
	const struct bpf_reg_val od = rd, os = *prs;

	const char *err = eval_divmod(op, &rd, prs, msk);

	/* the validator rejects exactly the constant-zero divisor... */
	assert((err != NULL) ==
		(od.u.min == od.u.max && os.u.min == os.u.max &&
		 os.u.max == 0));                       /* err_iff */
	if (err != NULL) {
		/* ...and leaves rd untouched on that path */
		assert(rd.u.min == od.u.min && rd.u.max == od.u.max &&
			rd.s.min == od.s.min && rd.s.max == od.s.max);
		return 0;                               /* err_frame */
	}

	/* cross-check of the intended postconditions */
	assert(is_scalar_or_pointer(rd.v.type));        /* type_ok */
	assert(range_ordering(&rd));                    /* uord + sord */
	assert(range_within_width(&rd, msk));           /* uwidth + swidth */
	assert(rd.v.type == od.v.type &&
		rd.v.size == od.v.size &&
		rd.v.buf_size == od.v.buf_size);        /* unchanged_v */
	assert(rd.mask == od.mask);                     /* unchanged_mask */

	/* concrete witnesses drawn from the UNSIGNED input ranges (div/mod
	 * are unsigned ops on the pattern); a zero divisor aborts the
	 * program at runtime (BPF_DIV_ZERO_CHECK), so only y >= 1 has a
	 * post-state to bound. */
	uint64_t ux = nondet_u64(), uy = nondet_u64();
	REQUIRE(od.u.min <= ux && ux <= od.u.max);
	REQUIRE(os.u.min <= uy && uy <= os.u.max);
	REQUIRE(1 <= uy);

	uint64_t ures = (op == BPF_DIV) ? ux / uy : ux % uy;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound */

	/* signed view: the canonical (sign-extended) value of the result
	 * pattern (mirrors eval_divmod_signed_soundness) */
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
