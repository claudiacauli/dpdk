#include <assert.h>
#include "eval_defined.h"

uint64_t nondet_u64(void);
int nondet_int(void);

static void havoc_reg(struct bpf_reg_val *rv)
{
	rv->v.type = (enum rte_bpf_arg_type)nondet_int();
	rv->v.size = nondet_u64();
	rv->v.buf_size = nondet_u64();
	rv->mask = nondet_u64();
	rv->s.min = nondet_u64();
	rv->s.max = nondet_u64();
	rv->u.min = nondet_u64();
	rv->u.max = nondet_u64();
}

int main(void)
{
	struct bpf_reg_val d, s;

	havoc_reg(&d);
	havoc_reg(&s);

	const struct bpf_reg_val *dst = nondet_int() ? &d : NULL;
	const struct bpf_reg_val *src = nondet_int() ? &s : NULL;

	const char *err = eval_defined(dst, src);

	int undef = (dst != NULL && dst->v.type == RTE_BPF_ARG_UNDEF) ||
		(src != NULL && src->v.type == RTE_BPF_ARG_UNDEF);
	assert((err != NULL) == undef);

#ifdef BMC_SANITY
	assert(0);
#endif

	return 0;
}
