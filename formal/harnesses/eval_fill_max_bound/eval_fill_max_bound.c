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
	ensures unchanged_size: rv->v.size == \old(rv->v.size);
	ensures unchanged_buf:  rv->v.buf_size == \old(rv->v.buf_size);
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures valid:      range_validity(rv, mask);
	ensures agree_min: min_agreement(rv, mask);
	ensures agree_max: max_agreement(rv, mask);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);
	ensures type_ok:    is_scalar_or_pointer(rv->v.type);

	// OP-OPTIMALITY: N/A -- a Top-producer (BOTH tracks to full width, plus stamps
	// type=RAW/mask); no endpoint-attainment notion. The full-width-BOTH output IS
	// self-optimal. optimality_notes.md §6h.
	//
	// SELF-OPTIMALITY: relayed from eval_max_bound's own selfopt clause -- the
	// type/mask stamps that follow touch neither track, so the reduced-element
	// property established there survives to this postcondition unchanged.
	ensures selfopt:    self_optimal(*rv, mask);
*/
void eval_fill_max_bound(struct bpf_reg_val *rv, uint64_t mask)
{
	eval_max_bound(rv, mask);
	rv->v.type = RTE_BPF_ARG_RAW;
	rv->mask = mask;
}
