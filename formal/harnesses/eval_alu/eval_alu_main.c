#include "eval_alu.h"

/*@assigns \nothing;*/
int main(void)
{
	struct bpf_eval_state st;
	struct bpf_verifier bvf;
	struct ebpf_insn ins;

	bvf.evst = &st;
	//@ admit BPF_CLASS(ins.code) == BPF_ALU || BPF_CLASS(ins.code) == EBPF_ALU64;
	//@ admit 0 <= ins.dst_reg < EBPF_REG_NUM && 0 <= ins.src_reg < EBPF_REG_NUM;
	/*@ admit \forall integer i; 0 <= i < EBPF_REG_NUM ==>
	      (st.rv[i].v.type == RTE_BPF_ARG_UNDEF ||
	       is_scalar_or_pointer(st.rv[i].v.type)) &&
	      range_ordering(&st.rv[i]) &&
	      (st.rv[i].mask == _32_BIT_MASK ||
	       st.rv[i].mask == _64_BIT_MASK) &&
	      unsigned_range_within_width(&st.rv[i], st.rv[i].mask) &&
	      signed_range_within_width(&st.rv[i], st.rv[i].mask); */
	eval_alu(&bvf, &ins);

	return 0;
}
