#include "eval_fill_imm64.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t mask, val;
	struct bpf_reg_val rv;
	//@ admit mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	//@ admit val <= mask;
	eval_fill_imm64(&rv, mask, val);

	return 0;
}
