#include "eval_umax_bound.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_reg_val rv;
	eval_umax_bound(&rv, _32_BIT_MASK);
	eval_umax_bound(&rv, _64_BIT_MASK);

	return 0;
}
