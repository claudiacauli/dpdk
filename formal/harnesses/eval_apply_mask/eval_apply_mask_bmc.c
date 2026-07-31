
#include <assert.h>
#include "eval_apply_mask.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

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

static void widen_witness_top(void)
{
	struct bpf_reg_val rv;
	rv.v.type = RTE_BPF_ARG_RAW;
	rv.v.size = 0;
	rv.v.buf_size = 0;
	rv.mask  = _32_BIT_MASK;
	rv.u.min = 0;
	rv.u.max = _32_BIT_MASK;
	rv.s.min = INT32_MIN;
	rv.s.max = INT32_MAX;

	const struct bpf_reg_val old = rv;
	const uint64_t wt = 0x80000000u;

	assert(range_ordering(&old));
	assert(range_agreement(&old, old.mask));
	assert(old.u.max <= old.mask);
	assert(old.u.min <= wt && wt <= old.u.max);
	assert((int64_t)wt - ((int64_t)old.mask + 1) == INT32_MIN);

	eval_apply_mask(&rv, _64_BIT_MASK);

	assert(rv.s.min == old.s.min && rv.s.max == old.s.max);
	assert(!(rv.s.min <= (int64_t)wt && (int64_t)wt <= rv.s.max));
	assert((int64_t)wt - rv.s.max == 1);
}

int main(void)
{
	widen_witness_top();

	struct bpf_reg_val rv;
	rv.v.type = RTE_BPF_ARG_RAW;
	rv.v.size = 0;
	rv.v.buf_size = 0;
	rv.mask  = _32_BIT_MASK;
	rv.u.min = 1075380245u;
	rv.u.max = 3222863894u;
	rv.s.min = -1072103403;
	rv.s.max = 1075380246;

	const struct bpf_reg_val old = rv;
	const uint64_t wt = 3222863893u;

	assert(wt <= old.mask);
	assert(old.u.min <= wt && wt <= old.u.max);
	const int64_t own_reading = (int64_t)wt - ((int64_t)old.mask + 1);
	assert(own_reading == -1072103403);
	assert(old.s.min <= own_reading && own_reading <= old.s.max);

	assert(range_ordering(&old));
	assert(range_agreement(&old, old.mask));
	assert(old.u.max <= old.mask);

	eval_apply_mask(&rv, _64_BIT_MASK);

	assert(rv.s.min == old.s.min && rv.s.max == old.s.max);
	const int64_t true_reading = (int64_t)wt;
	assert(true_reading == 3222863893);

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

	REQUIRE(rv.u.min <= rv.u.max && rv.s.min <= rv.s.max);

	REQUIRE(rv.mask == _32_BIT_MASK || rv.mask == _64_BIT_MASK);
	REQUIRE(rv.u.max <= rv.mask);

	const struct bpf_reg_val old = rv;

	uint64_t wx = nondet_u64();
	REQUIRE(old.u.min <= wx && wx <= old.u.max);
	int64_t wv = nondet_i64();
	REQUIRE(old.s.min <= wv && wv <= old.s.max);

	REQUIRE(old.u.min <= (uint64_t)wv && (uint64_t)wv <= old.u.max);

#ifdef BMC_WSOUND

	uint64_t wt = nondet_u64();
	REQUIRE(old.mask == _32_BIT_MASK || old.mask == _64_BIT_MASK);

	REQUIRE(old.u.max <= old.mask);
	REQUIRE(-(int64_t)(old.mask >> 1) - 1 <= old.s.min &&
		old.s.max <= (int64_t)(old.mask >> 1));
	REQUIRE(range_agreement(&old, old.mask));

	REQUIRE(mask <= old.mask);
	REQUIRE(wt <= old.mask);
	REQUIRE(old.u.min <= wt && wt <= old.u.max);
	int64_t wtc = (wt <= (old.mask >> 1)) ? (int64_t)wt
					      : (int64_t)(wt - (old.mask + 1));
	REQUIRE(old.s.min <= wtc && wtc <= old.s.max);
#endif

	eval_apply_mask(&rv, mask);

	assert(mask != _64_BIT_MASK ||
		rv.u.min == old.u.min);
	assert(mask != _64_BIT_MASK ||
		rv.u.max == old.u.max);

	assert(!(mask == _32_BIT_MASK &&
		old.u.min / (mask + 1) != old.u.max / (mask + 1)) ||
		(rv.u.min == 0 && rv.u.max == mask));
	assert(!(mask == _32_BIT_MASK &&
		old.u.min / (mask + 1) == old.u.max / (mask + 1)) ||
		(rv.u.min == (old.u.min & mask) &&
		 rv.u.max == (old.u.max & mask)));
	assert(rv.mask == mask);
	assert(rv.mask == _32_BIT_MASK ||
		rv.mask == _64_BIT_MASK);
	int64_t sxu_min = (rv.u.min <= (mask >> 1)) ? (int64_t)rv.u.min
			: (int64_t)(rv.u.min - (mask + 1));
	int64_t sxu_max = (rv.u.max <= (mask >> 1)) ? (int64_t)rv.u.max
			: (int64_t)(rv.u.max - (mask + 1));
	assert(mask != _32_BIT_MASK ||
		rv.s.min == INT32_MIN || rv.s.min == old.s.min ||
		rv.s.min == sxu_min);
	assert(mask != _32_BIT_MASK ||
		rv.s.max == INT32_MAX || rv.s.max == old.s.max ||
		rv.s.max == sxu_max);
	assert(mask != _64_BIT_MASK ||
		rv.s.min == INT64_MIN || rv.s.min == old.s.min ||
		rv.s.min == sxu_min);
	assert(mask != _64_BIT_MASK ||
		rv.s.max == INT64_MAX || rv.s.max == old.s.max ||
		rv.s.max == sxu_max);
	assert(rv.v.type == old.v.type &&
		rv.v.size == old.v.size &&
		rv.v.buf_size == old.v.buf_size);
	assert(rv.u.min <= rv.u.max);
	assert(rv.s.min <= rv.s.max);
	assert(rv.u.max <= mask);
	assert(-(int64_t)(mask >> 1) - 1 <= rv.s.min &&
		rv.s.max <= (int64_t)(mask >> 1));

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
			((uint64_t)rv.s.min & mask));
		assert(!(old_agree && old_width) || !det || rv.u.max ==
			((uint64_t)rv.s.max & mask));
	}
	uint64_t mx = wx & mask;
	assert(rv.u.min <= mx && mx <= rv.u.max);
	uint64_t sm = ((uint64_t)wv) & mask;
	int64_t sv = (sm <= (mask >> 1)) ? (int64_t)sm
					 : (int64_t)(sm - (mask + 1));
	assert(rv.s.min <= sv && sv <= rv.s.max);

#ifdef BMC_WSOUND
	uint64_t wtm = wt & mask;
	assert(rv.u.min <= wtm && wtm <= rv.u.max);
	int64_t wts = (wtm <= (mask >> 1)) ? (int64_t)wtm
					   : (int64_t)(wtm - (mask + 1));
	assert(rv.s.min <= wts && wts <= rv.s.max);
#endif

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
#endif
