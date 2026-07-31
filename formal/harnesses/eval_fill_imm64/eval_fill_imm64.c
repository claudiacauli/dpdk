#include "eval_fill_imm64.h"

#ifdef FIX_FILL_IMM_SIGNED_32

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires 0 <= p <= mask;
	assigns \nothing;
	ensures \result == to_signed(p, mask);
*/
static int64_t fi_sext(uint64_t p, uint64_t mask)
{
	return (p <= (mask >> 1)) ? (int64_t)p : (int64_t)(p - (mask + 1));
}
#endif

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires 0 <= val <= mask;
	requires \valid(rv);
	terminates \true;
	assigns rv->mask, rv->s, rv->u;

	ensures mask_set:   rv->mask == mask;
	ensures const_u:    rv->u.min == val && rv->u.max == val;
	ensures const_s:    rv->s.min == to_signed(val, mask) &&
			rv->s.max == rv->s.min;
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);

	ensures selfopt:    self_optimal(*rv, mask);
*/
void
eval_fill_imm64(struct bpf_reg_val *rv, uint64_t mask, uint64_t val)
{
	rv->mask = mask;
#ifdef FIX_FILL_IMM_SIGNED_32

	rv->s.min = fi_sext(val, mask);
	rv->s.max = rv->s.min;
#else
	rv->s.min = val;
	rv->s.max = val;
#endif
	rv->u.min = val;
	rv->u.max = val;
}
