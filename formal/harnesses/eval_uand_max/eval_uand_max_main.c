#include "eval_uand_max.h"

/*@assigns \nothing;*/
int main(void)
{
	uint64_t v1, v2;
	size_t opsz;
	//@ admit opsz == 32 || opsz == 64;
	eval_uand_max(v1, v2, opsz);

	return 0;
}
