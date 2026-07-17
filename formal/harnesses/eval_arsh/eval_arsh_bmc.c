#include <assert.h>
#include "eval_arsh.h"

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

	size_t opsz = nondet_size_t();
	REQUIRE(msk != _32_BIT_MASK || opsz == 32);
	REQUIRE(msk != _64_BIT_MASK || opsz == 64);

	/* BPF allows `arsh rX, rX`, but eval_alu always hands eval_arsh a
	 * fresh local copy of the source register, never rd itself. Aliasing
	 * rd here would make the later shifts read already-shifted bounds —
	 * a call pattern the real caller cannot produce (spurious failures
	 * for shift ops). */
	const struct bpf_reg_val *prs = &rs;

	/* requires clauses of eval_arsh */
	REQUIRE(is_scalar_or_pointer(rd.v.type));
	REQUIRE(is_scalar_or_pointer(prs->v.type));
	REQUIRE(range_validity(&rd, msk) && range_validity(prs, msk));
	REQUIRE(range_within_width(&rd, msk) && range_within_width(prs, msk));

	/* \old(*rd), \old(*rs) */
	const struct bpf_reg_val od = rd, os = *prs;

	/* concrete witnesses for the \forall of the two predicates: value
	 * witnesses x (signed track) / ux (unsigned track), shift-amount
	 * witness uy — both predicates quantify the amount over os.u */
	int64_t x = nondet_i64();
	REQUIRE(od.s.min <= x && x <= od.s.max);

	uint64_t ux = nondet_u64(), uy = nondet_u64();
	REQUIRE(od.u.min <= ux && ux <= od.u.max);
	REQUIRE(os.u.min <= uy && uy <= os.u.max);

	eval_arsh(&rd, prs, opsz, msk);

	/* cross-check of the WP-proved postconditions */
	assert(is_scalar_or_pointer(rd.v.type));        /* type_ok */
	assert(range_ordering(&rd));                    /* ord     */
	assert(range_within_width(&rd, msk));           /* uwidth + swidth */
	assert(rd.v.type == od.v.type &&
		rd.v.size == od.v.size &&
		rd.v.buf_size == od.v.buf_size);        /* unchanged_v */
	assert(rd.mask == od.mask);                     /* unchanged_mask */

	/* soundness witnesses cover in-range shift amounts only */
	REQUIRE(uy < opsz);

	/* signed (arithmetic) shift of the canonical value: stays canonical */
	int64_t s_val = x >> uy;   /* gcc/clang: arithmetic shift */
	assert(rd.s.min <= s_val && s_val <= rd.s.max);        /* ssound */

	/* unsigned view: sign-extend the pattern ux, arithmetic-shift,
	 * re-encode as a w-bit pattern */
	int64_t sx = (ux <= (msk >> 1)) ? (int64_t)ux
					: (int64_t)(ux - (msk + 1));
	uint64_t ures = (uint64_t)(sx >> uy) & msk;
	assert(rd.u.min <= ures && ures <= rd.u.max);          /* usound */

#ifdef BMC_SANITY
	/* must FAIL: proves the preconditions are satisfiable and the
	 * asserts above are reachable */
	assert(0);
#endif

	return 0;
}
