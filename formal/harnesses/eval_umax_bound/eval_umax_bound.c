#include "eval_umax_bound.h"

/*@
	requires \valid(rv);
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
    	terminates \true;
	assigns rv->u.min, rv->u.max;

	ensures ufull:      rv->u.min == 0 && rv->u.max == mask;
	ensures umax_ok:    rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures unchanged_s:    rv->s == \old(rv->s);
	ensures unchanged_mask: rv->mask == \old(rv->mask);
	ensures unchanged_v:    rv->v == \old(rv->v);
	ensures uord:       unsigned_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
*/
void eval_umax_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	rv->u.max = mask;
	rv->u.min = 0;
}
