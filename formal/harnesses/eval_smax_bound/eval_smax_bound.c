#include "eval_smax_bound.h"

/*@
	requires \valid(rv);
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	terminates \true;
	assigns rv->s.min, rv->s.max;
	ensures mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	ensures mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
	ensures rv->v == \old(rv->v);
	ensures rv->s.min <= rv->s.max;
*/
void eval_smax_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	rv->s.max = mask >> 1;
	rv->s.min = rv->s.max ^ UINT64_MAX;
	//@ assert mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN;
	//@ assert mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN;
}

