#include "eval_defined.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_reg_val d, s;

	eval_defined(&d, &s);
	eval_defined(&d, NULL);
	eval_defined(NULL, &s);
	eval_defined(NULL, NULL);

	return 0;
}
