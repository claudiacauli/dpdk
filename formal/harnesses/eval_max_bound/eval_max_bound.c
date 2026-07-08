#include "eval_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max;
	ensures rv->u.min == 0 && rv->u.max == mask;
	ensures rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	ensures mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
	ensures rv->mask == \old(rv->mask);
	ensures rv->v == \old(rv->v);
	ensures rv->u.min <= rv->u.max;
	ensures rv->s.min <= rv->s.max;
*/
void eval_max_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	//@ assert mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	eval_umax_bound(rv, mask);
	//@ assert rv->u.min == 0;
	//@ assert rv->u.max == mask;
	//@ assert rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	eval_smax_bound(rv, mask);
	//@ assert mask == _32_BIT_MASK ==> rv->s.max == INT32_MAX;
	//@ assert mask == _64_BIT_MASK ==> rv->s.max == INT64_MAX;
	//@ assert mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	//@ assert mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
}
