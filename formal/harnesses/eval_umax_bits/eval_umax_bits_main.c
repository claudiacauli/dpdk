#include "eval_umax_bits.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t v;
	size_t opsz;
	//@ admit opsz == 32 || opsz == 64;
	eval_umax_bits(v, opsz);

	return 0;
}
