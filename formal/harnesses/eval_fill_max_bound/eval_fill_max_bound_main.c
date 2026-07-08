#include "eval_fill_max_bound.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_reg_val rv;
	eval_fill_max_bound(&rv, _32_BIT_MASK);
	eval_fill_max_bound(&rv, _64_BIT_MASK);

	return 0;
}
