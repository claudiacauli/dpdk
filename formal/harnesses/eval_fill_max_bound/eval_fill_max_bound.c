#include "eval_fill_max_bound.h"
#include "../eval_max_bound/eval_max_bound.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->u.min, rv->u.max, rv->s.min, rv->s.max, rv->v.type, rv->mask;

	ensures ufull:      rv->u.min == 0 && rv->u.max == mask;
	ensures umax_ok:    rv->u.max == _32_BIT_MASK || rv->u.max == _64_BIT_MASK;
	ensures sfull32:    mask == _32_BIT_MASK ==> rv->s.min == INT32_MIN && rv->s.max == INT32_MAX;
	ensures sfull64:    mask == _64_BIT_MASK ==> rv->s.min == INT64_MIN && rv->s.max == INT64_MAX;
	ensures mask_set:   rv->mask == mask;
	ensures mask_ok:    rv->mask == _32_BIT_MASK || rv->mask == _64_BIT_MASK;
	ensures type_raw:   rv->v.type == RTE_BPF_ARG_RAW;
	ensures frame_size: rv->v.size == \old(rv->v.size);
	ensures frame_buf:  rv->v.buf_size == \old(rv->v.buf_size);
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures valid:      range_validity(rv, mask);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
	ensures type_ok:    is_scalar_or_pointer(rv->v.type);
*/
void eval_fill_max_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	eval_max_bound(rv, mask);
	rv->v.type = RTE_BPF_ARG_RAW;
	rv->mask = mask;
}
