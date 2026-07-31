#include <assert.h>
#include "eval_uor_max.h"

uint64_t nondet_u64(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

int main(void)
{
	size_t opsz = nondet_size_t();
	REQUIRE(opsz == 32 || opsz == 64);

	uint64_t msk = (opsz == 32) ? UINT32_MAX : UINT64_MAX;

	uint64_t v1 = nondet_u64(), v2 = nondet_u64();
	REQUIRE(v1 <= msk && v2 <= msk);

	uint64_t a = nondet_u64(), b = nondet_u64();
	REQUIRE(a <= v1 && b <= v2);

	uint64_t r = eval_uor_max(v1, v2, opsz);

	assert(0 <= r);
	assert(r <= msk);
	assert((a | b) <= r);
	assert((a ^ b) <= r);
	assert((r & (r + 1)) == 0);
	assert((r >> 1) <= v1 || (r >> 1) <= v2);

	if (v1 <= (msk >> 1) && v2 <= (msk >> 1))
		assert(r <= (msk >> 1));

#ifdef BMC_SANITY

	assert(0);
#endif

	return 0;
}
