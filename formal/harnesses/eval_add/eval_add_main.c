#include "eval_add.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t mask;
	struct bpf_reg_val rd, rs;
	//@ admit mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	//@ admit range_validity(&rd, mask);
	//@ admit range_validity(&rs, mask);
	//@ admit range_within_width(&rd, mask);
	//@ admit range_within_width(&rs, mask);
	//@ admit is_scalar_or_pointer(rd.v.type);
	//@ admit is_scalar_or_pointer(rs.v.type);
	eval_add(&rd, &rs, mask);

	return 0;
}
