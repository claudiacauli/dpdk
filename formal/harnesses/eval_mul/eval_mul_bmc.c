#include <assert.h>
#include "eval_mul.h"

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
	struct bpf_reg_val rd, rs;

	havoc_reg(&rd);
	havoc_reg(&rs);

	uint64_t msk = nondet_u64();
	REQUIRE(msk == _32_BIT_MASK || msk == _64_BIT_MASK);
#ifdef BMC_32
	/* restrict to opsz==32: 32-bit products are cheap for the bit-vector
	 * solver where 64-bit symbolic multiplies blow up. S1 (missing sign
	 * extension) manifests exactly here. */
	REQUIRE(msk == _32_BIT_MASK);
#endif

	size_t opsz = nondet_size_t();
	REQUIRE(msk != _32_BIT_MASK || opsz == 32);
	REQUIRE(msk != _64_BIT_MASK || opsz == 64);

	/* eval_alu always hands eval_mul a fresh local copy of the source
	 * register, and the WP contract requires \separated(rd, rs) */
	const struct bpf_reg_val *prs = &rs;

	/* requires clauses */
	REQUIRE(is_scalar_or_pointer(rd.v.type));
	REQUIRE(is_scalar_or_pointer(prs->v.type));
	REQUIRE(range_validity(&rd, msk) && range_validity(prs, msk));
	REQUIRE(range_within_width(&rd, msk) && range_within_width(prs, msk));

	/* \old(*rd), \old(*rs) */
	const struct bpf_reg_val od = rd, os = *prs;

	/* concrete witnesses: unsigned patterns for the u track, signed
	 * values (BOTH sides) for the s track — multiply is arithmetic.
	 * BMC_U_ONLY / BMC_S_ONLY isolate one track's products so the
	 * bit-vector solver has fewer symbolic 64-bit multiplies per query. */
#ifndef BMC_S_ONLY
	uint64_t ux = nondet_u64(), uy = nondet_u64();
	REQUIRE(od.u.min <= ux && ux <= od.u.max);
	REQUIRE(os.u.min <= uy && uy <= os.u.max);
#endif
#ifndef BMC_U_ONLY
	int64_t sv = nondet_i64(), sw = nondet_i64();
	REQUIRE(od.s.min <= sv && sv <= od.s.max);
	REQUIRE(os.s.min <= sw && sw <= os.s.max);
#endif

	eval_mul(&rd, prs, opsz, msk);

	/* cross-check of the intended postconditions */
	assert(is_scalar_or_pointer(rd.v.type));        /* type_ok */
	assert(range_ordering(&rd));                    /* ord     */
	assert(range_within_width(&rd, msk));           /* uwidth + swidth */
	assert(rd.v.type == od.v.type &&
		rd.v.size == od.v.size &&
		rd.v.buf_size == od.v.buf_size);        /* unchanged_v */
	assert(rd.mask == od.mask);                     /* unchanged_mask */

#ifndef BMC_S_ONLY
	/* unsigned view: low-w bits of the product */
	uint64_t ures = (ux * uy) & msk;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound */
#endif

#ifndef BMC_U_ONLY
	/* signed view: low-w bits of the signed product, sign-extended
	 * (mirrors eval_mul_signed_soundness: to_signed((v * w) & msk, msk)) */
	uint64_t sres = ((uint64_t)sv * (uint64_t)sw) & msk;
	int64_t s_val = (sres <= (msk >> 1)) ? (int64_t)sres
					     : (int64_t)(sres - (msk + 1));
	assert(rd.s.min <= s_val && s_val <= rd.s.max);        /* ssound */
#endif

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
