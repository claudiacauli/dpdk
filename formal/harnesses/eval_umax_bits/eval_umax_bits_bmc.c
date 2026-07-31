#include <assert.h>
#include "eval_umax_bits.h"

uint64_t nondet_u64(void);
size_t nondet_size_t(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

int main(void)
{
	size_t opsz = nondet_size_t();
	REQUIRE(opsz == 32 || opsz == 64);

	uint64_t msk = (opsz == 32) ? UINT32_MAX : UINT64_MAX;

	uint64_t v = nondet_u64();
	REQUIRE(v <= msk);

	uint64_t r = eval_umax_bits(v, opsz);

	if (v == 0)
		assert(r == 0);
	assert(v <= r);
	assert((r & (r + 1)) == 0);
	assert(r <= msk);
	if (v != 0)
		assert((r >> 1) <= v);

#ifdef BMC_SANITY

	assert(0);
#endif

	return 0;
}
