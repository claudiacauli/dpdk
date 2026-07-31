#include "eval_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max;

	ensures ufull:      rv->u.min == 0 && rv->u.max == mask;
	ensures umax_ok:    rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures sfull32:    mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	ensures sfull64:    mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
	ensures unchanged_mask: rv->mask == \old(rv->mask);
	ensures unchanged_v:    rv->v == \old(rv->v);
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures valid:      range_validity(rv, mask);
	ensures agree_min: min_agreement(rv, mask);
	ensures agree_max: max_agreement(rv, mask);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);

	ensures selfopt:    self_optimal(*rv, mask);
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
