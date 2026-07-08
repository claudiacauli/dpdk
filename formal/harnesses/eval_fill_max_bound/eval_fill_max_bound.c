#include "eval_fill_max_bound.h"
#include "../eval_max_bound/eval_max_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->v.type, rv->mask;
	ensures rv->u.min == 0 && rv->u.max == mask;
	ensures rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	ensures mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
	ensures rv->mask == mask;
	ensures rv->mask == _32_BIT_MASK || rv->mask == _64_BIT_MASK;
	ensures rv->v.type == RTE_BPF_ARG_RAW;
	ensures rv->v.size == \old(rv->v.size);
	ensures rv->v.buf_size == \old(rv->v.buf_size);
	ensures rv->u.min <= rv->u.max;
	ensures rv->s.min <= rv->s.max;
*/
void eval_fill_max_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	eval_max_bound(rv, mask);
	rv->v.type = RTE_BPF_ARG_RAW;
	rv->mask = mask;
}
