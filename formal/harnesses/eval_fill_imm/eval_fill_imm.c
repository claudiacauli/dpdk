#include "eval_fill_imm.h"
#include "../eval_fill_imm64/eval_fill_imm64.h"

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires \valid(rv);
	terminates \true;
	assigns rv->v.type, rv->mask, rv->s, rv->u;

	ensures type_raw:   rv->v.type == RTE_BPF_ARG_RAW;
	ensures type_ok:    is_scalar_or_pointer(rv->v.type);
	ensures mask_set:   rv->mask == mask;
	ensures const_u:    rv->u.min == (((uint64_t)imm) & mask) &&
			rv->u.max == rv->u.min;
	ensures const_s:    rv->s.min == to_signed(((uint64_t)imm) & mask, mask) &&
			rv->s.max == rv->s.min;
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
	ensures agree_min: min_agreement(rv, mask);
	ensures agree_max: max_agreement(rv, mask);
	ensures valid:      range_validity(rv, mask);
*/
void
eval_fill_imm(struct bpf_reg_val *rv, uint64_t mask, int32_t imm)
{
	uint64_t v;

	v = (uint64_t)imm & mask;

	rv->v.type = RTE_BPF_ARG_RAW;
	eval_fill_imm64(rv, mask, v);
}
