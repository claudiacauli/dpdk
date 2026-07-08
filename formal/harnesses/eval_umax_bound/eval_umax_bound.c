#include "eval_umax_bound.h"

/*@
	requires \valid(rv);
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
    	terminates \true;
	assigns rv->u.min, rv->u.max;
	ensures rv->u.min == 0 && rv->u.max == mask;
	ensures rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures rv->s == \old(rv->s);
	ensures rv->mask == \old(rv->mask);
	ensures rv->v == \old(rv->v);
	ensures rv->u.min <= rv->u.max;
*/
void eval_umax_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	rv->u.max = mask;
	rv->u.min = 0;
}
