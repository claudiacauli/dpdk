#include "eval_neg.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t mask;
	size_t opsz;
	struct bpf_reg_val rd;
	//@ admit mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	//@ admit opsz == 32 || opsz == 64;
	//@ admit range_validity(&rd, mask);
	//@ admit range_within_width(&rd, mask);
	//@ admit is_scalar_or_pointer(rd.v.type);
	eval_neg(&rd, opsz, mask);

	return 0;
}
