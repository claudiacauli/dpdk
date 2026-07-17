#include "eval_fill_imm.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t mask;
	int32_t imm;
	struct bpf_reg_val rv;
	//@ admit mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	eval_fill_imm(&rv, mask, imm);

	return 0;
}
