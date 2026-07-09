#include "eval_apply_mask.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_reg_val rv;
	uint64_t mask;
	//@ admit mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	//@ admit range_ordering(&rv);
	eval_apply_mask(&rv, mask);

	return 0;
}
