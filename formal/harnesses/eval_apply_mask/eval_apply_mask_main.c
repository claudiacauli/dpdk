#include "eval_apply_mask.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_reg_val rv;
	//@ admit rv.u.min <= rv.u.max;
	//@ admit rv.s.min <= rv.s.max;
	eval_apply_mask(&rv, _32_BIT_MASK);
	eval_apply_mask(&rv, _64_BIT_MASK);

	return 0;
}
