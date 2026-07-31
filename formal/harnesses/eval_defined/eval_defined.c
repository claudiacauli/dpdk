#include "eval_defined.h"

/*@
	requires dst == \null || \valid_read(dst);
	requires src == \null || \valid_read(src);
	terminates \true;
	assigns \nothing;
	ensures def_iff: (\result != \null) <==>
		((dst != \null && dst->v.type == RTE_BPF_ARG_UNDEF) ||
		 (src != \null && src->v.type == RTE_BPF_ARG_UNDEF));

*/
const char *
eval_defined(const struct bpf_reg_val *dst, const struct bpf_reg_val *src)
{
	if (dst != NULL && dst->v.type == RTE_BPF_ARG_UNDEF)
		return "dest reg value is undefined";
	if (src != NULL && src->v.type == RTE_BPF_ARG_UNDEF)
		return "src reg value is undefined";
	return NULL;
}
