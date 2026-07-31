#include "eval_alu.h"
#include "../eval_defined/eval_defined.h"
#include "axioms_alu.h"
#include "lemmas_deliver.h"
#include "../eval_apply_mask/eval_apply_mask.h"
#include "../eval_fill_imm/eval_fill_imm.h"
#include "../eval_add/eval_add.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_lsh/eval_lsh.h"
#include "../eval_rsh/eval_rsh.h"
#include "../eval_arsh/eval_arsh.h"
#include "../eval_and/eval_and.h"
#include "../eval_or/eval_or.h"
#include "../eval_xor/eval_xor.h"
#include "../eval_mul/eval_mul.h"
#include "../eval_divmod/eval_divmod.h"
#include "../eval_neg/eval_neg.h"
#include "../eval_max_bound/eval_max_bound.h"

/*@
	requires \valid(bvf) && \valid(bvf->evst) && \valid_read(ins);
	requires \valid(&bvf->evst->rv[0 .. EBPF_REG_NUM - 1]);
	requires \separated(bvf, bvf->evst, ins);
	requires \separated(&bvf->evst->rv[0 .. EBPF_REG_NUM - 1], ins);

	requires cls_ok: BPF_CLASS(ins->code) == BPF_ALU ||
		BPF_CLASS(ins->code) == EBPF_ALU64;
	requires idx_ok: 0 <= ins->dst_reg < EBPF_REG_NUM &&
		0 <= ins->src_reg < EBPF_REG_NUM;
	requires ops_scalar: is_scalar(bvf->evst->rv[ins->dst_reg].v.type) &&
		(BPF_SRC(ins->code) == BPF_X ==>
			is_scalar(bvf->evst->rv[ins->src_reg].v.type));
	requires regs_ok: \forall integer i; 0 <= i < EBPF_REG_NUM ==>
		is_scalar_or_pointer(bvf->evst->rv[i].v.type) &&
		range_ordering(&bvf->evst->rv[i]) &&
		(bvf->evst->rv[i].mask == _32_BIT_MASK ||
		 bvf->evst->rv[i].mask == _64_BIT_MASK) &&
		unsigned_range_within_width(&bvf->evst->rv[i],
			bvf->evst->rv[i].mask) &&
		signed_range_within_width(&bvf->evst->rv[i],
			bvf->evst->rv[i].mask);
	terminates \true;
	assigns bvf->evst->rv[ins->dst_reg];

	ensures err_def: alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type))
		==> \result != \null;
	ensures err_dom: \result != \null ==>
		alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type)) ||
		BPF_OP(ins->code) == BPF_DIV || BPF_OP(ins->code) == BPF_MOD;
	ensures noerr: !alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type)) &&
		BPF_OP(ins->code) != BPF_DIV && BPF_OP(ins->code) != BPF_MOD
		==> \result == \null;

	ensures type_ok: \result == \null ==>
		is_scalar(bvf->evst->rv[ins->dst_reg].v.type);
	ensures uord: \result == \null ==>
		unsigned_range_ordering(&bvf->evst->rv[ins->dst_reg]);
	ensures sord: \result == \null ==>
		signed_range_ordering(&bvf->evst->rv[ins->dst_reg]);
	ensures uwidth: \result == \null ==>
		unsigned_range_within_width(&bvf->evst->rv[ins->dst_reg],
			alu_msk(ins->code));
	ensures swidth: \result == \null ==>
		signed_range_within_width(&bvf->evst->rv[ins->dst_reg],
			alu_msk(ins->code));

	ensures usound: \result == \null && !alu_selfxor(*ins) ==>
		eval_alu_unsigned_soundness(
			\old(bvf->evst->rv[ins->dst_reg]),
			\old(bvf->evst->rv[ins->src_reg]),
			*ins, bvf->evst->rv[ins->dst_reg]);
	ensures ssound: \result == \null && !alu_selfxor(*ins) ==>
		eval_alu_signed_soundness(
			\old(bvf->evst->rv[ins->dst_reg]),
			\old(bvf->evst->rv[ins->src_reg]),
			*ins, bvf->evst->rv[ins->dst_reg]);
*/
const char *
eval_alu(struct bpf_verifier *bvf, const struct ebpf_insn *ins)
{
	uint64_t msk;
	uint32_t op;
	size_t opsz, sz;
	const char *err;
	struct bpf_eval_state *st;
	struct bpf_reg_val *rd, rs;

	sz = (BPF_CLASS(ins->code) == BPF_ALU) ?
		sizeof(uint32_t) : sizeof(uint64_t);
	opsz = sz * CHAR_BIT;
	msk = RTE_LEN2MASK(opsz, uint64_t);

	st = bvf->evst;
	rd = st->rv + ins->dst_reg;

	/*@ assert inv_d: is_scalar(rd->v.type); */
	/*@ assert inv_s: BPF_SRC(ins->code) == BPF_X ==>
	      is_scalar(st->rv[ins->src_reg].v.type); */
	/*@ assert ord_d: range_ordering(rd); */
	/*@ assert ord_s: range_ordering(&st->rv[ins->src_reg]); */

	if (BPF_SRC(ins->code) == BPF_X) {
		rs = st->rv[ins->src_reg];
		eval_apply_mask(&rs, msk);
		/*@ assert wc_s: alu_wit_covers(
		      \at(bvf->evst->rv[ins->src_reg], Pre), rs, msk); */
		/*@ assert ord_dx_u: unsigned_range_ordering(rd); */
		/*@ assert ord_dx_s: signed_range_ordering(rd); */
	} else {
		rs = (struct bpf_reg_val){.v = {.size = sz,},};
		eval_fill_imm(&rs, msk, ins->imm);
		/*@ assert ic_s: alu_imm_covers(rs, *ins, msk); */
		/*@ assert ord_dk_u: unsigned_range_ordering(rd); */
		/*@ assert ord_dk_s: signed_range_ordering(rd); */
	}

	PreMask: eval_apply_mask(rd, msk);

	/*@ assert wc_d: alu_wit_covers(\at(*rd, PreMask), *rd, msk); */
	/*@ assert pin_d_mask: \at(rd->mask, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].mask, Pre); */
	/*@ assert pin_d_umin: \at(rd->u.min, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].u.min, Pre); */
	/*@ assert pin_d_umax: \at(rd->u.max, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].u.max, Pre); */
	/*@ assert pin_d_smin: \at(rd->s.min, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].s.min, Pre); */
	/*@ assert pin_d_smax: \at(rd->s.max, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].s.max, Pre); */
	/*@ assert wc_d_pre: alu_wit_covers(
	      \at(bvf->evst->rv[ins->dst_reg], Pre), *rd, msk); */

	/*@ assert ty_d: rd->v.type ==
	      \at(bvf->evst->rv[ins->dst_reg].v.type, Pre); */
	/*@ assert ty_s: BPF_SRC(ins->code) == BPF_X ==>
	      rs.v.type == \at(bvf->evst->rv[ins->src_reg].v.type, Pre); */
	/*@ assert ty_k: BPF_SRC(ins->code) != BPF_X ==>
	      rs.v.type == RTE_BPF_ARG_RAW; */

	op = BPF_OP(ins->code);

	if (op == BPF_XOR && BPF_SRC(ins->code) == BPF_X &&
	    ins->src_reg == ins->dst_reg) {
		eval_fill_imm(&rs, UINT64_MAX, 0);
		eval_fill_imm(rd, UINT64_MAX, 0);
		/*@ assert ty_sx: rd->v.type == RTE_BPF_ARG_RAW &&
		      rs.v.type == RTE_BPF_ARG_RAW; */
		/*@ assert sx_rs_zero: rs.u.min == 0 && rs.u.max == 0 &&
		      rs.s.min == 0 && rs.s.max == 0; */
		/*@ assert sx_rd_zero: rd->u.min == 0 && rd->u.max == 0 &&
		      rd->s.min == 0 && rd->s.max == 0; */
		/*@ assert sx_vld32_rs: msk == _32_BIT_MASK ==>
		      range_validity(&rs, msk); */
		/*@ assert sx_vld32_rd: msk == _32_BIT_MASK ==>
		      range_validity(rd, msk); */
		/*@ assert sx_vld64_rs: msk == _64_BIT_MASK ==>
		      range_validity(&rs, msk); */
		/*@ assert sx_vld64_rd: msk == _64_BIT_MASK ==>
		      range_validity(rd, msk); */
		/*@ assert sx_wid32: msk == _32_BIT_MASK ==>
		      range_within_width(&rs, msk) &&
		      range_within_width(rd, msk); */
		/*@ assert sx_wid64: msk == _64_BIT_MASK ==>
		      range_within_width(&rs, msk) &&
		      range_within_width(rd, msk); */
	}

	err = eval_defined((op != EBPF_MOV) ? rd : NULL,
			   (op != BPF_NEG) ? &rs : NULL);
	if (err != NULL)
		return err;

	/*@ assert ord_d2: range_ordering(rd); */
	/*@ assert wid_d: range_within_width(rd, msk); */
	/*@ assert sc_d: is_scalar(rd->v.type); */
	/*@ assert sc_s: is_scalar(rs.v.type); */
	/*@ assert ord_s2: range_ordering(&rs); */
	/*@ assert sep_rs: \separated(&rs, rd); */
	/*@ assert sep_rs_evst: \separated(&rs, &bvf->evst->rv[0 ..
	      EBPF_REG_NUM - 1]); */

	/*@ assert wc_d2: !alu_selfxor(*ins) ==> alu_wit_covers(
	      \at(bvf->evst->rv[ins->dst_reg], Pre), *rd, msk); */
	/*@ assert wc_s2: !alu_selfxor(*ins) && BPF_SRC(ins->code) == BPF_X ==>
	      alu_wit_covers(\at(bvf->evst->rv[ins->src_reg], Pre), rs, msk); */
	/*@ assert ic_s2: BPF_SRC(ins->code) != BPF_X ==>
	      alu_imm_covers(rs, *ins, msk); */
	/*@ assert cpre: !alu_selfxor(*ins) && msk == alu_msk(ins->code) ==>
	      alu_compose_pre(\at(bvf->evst->rv[ins->dst_reg], Pre),
	                      \at(bvf->evst->rv[ins->src_reg], Pre),
	                      *rd, rs, *ins, msk); */
	/*@ assert wid_s32: msk == _32_BIT_MASK ==>
	      range_within_width(&rs, msk); */
	/*@ assert wid_s64: msk == _64_BIT_MASK ==>
	      range_within_width(&rs, msk); */

	if (op == BPF_ADD) {
		eval_add(rd, &rs, msk);
		/*@ assert us_add: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_add: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_SUB) {
		eval_sub(rd, &rs, msk);
		/*@ assert us_sub: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_sub: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_LSH) {
		eval_lsh(rd, &rs, opsz, msk);
		/*@ assert us_lsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_lsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_RSH) {
		eval_rsh(rd, &rs, opsz, msk);
		/*@ assert us_rsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_rsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == EBPF_ARSH) {
		eval_arsh(rd, &rs, opsz, msk);
		/*@ assert us_arsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_arsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_AND) {
		eval_and(rd, &rs, opsz, msk);
		/*@ assert us_and: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_and: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_OR) {
		eval_or(rd, &rs, opsz, msk);
		/*@ assert us_or: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_or: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_XOR) {
		eval_xor(rd, &rs, opsz, msk);
		/*@ assert us_xor: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_xor: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_MUL) {
		eval_mul(rd, &rs, opsz, msk);
		/*@ assert us_mul: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_mul: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_DIV || op == BPF_MOD) {
		err = eval_divmod(op, rd, &rs, msk);
		/*@ assert us_divmod: !alu_selfxor(*ins) && err == \null ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_divmod: !alu_selfxor(*ins) && err == \null ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_NEG) {
		eval_neg(rd, opsz, msk);
		/*@ assert us_neg: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_neg: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == EBPF_MOV) {
		*rd = rs;
		/*@ assert us_mov: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_mov: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else {
		eval_max_bound(rd, msk);
	}

	/*@ assert us_all: !alu_selfxor(*ins) && err == \null ==>
	      eval_alu_unsigned_soundness(
	        \at(bvf->evst->rv[ins->dst_reg], Pre),
	        \at(bvf->evst->rv[ins->src_reg], Pre), *ins,
	        bvf->evst->rv[ins->dst_reg]); */
	/*@ assert ss_all: !alu_selfxor(*ins) && err == \null ==>
	      eval_alu_signed_soundness(
	        \at(bvf->evst->rv[ins->dst_reg], Pre),
	        \at(bvf->evst->rv[ins->src_reg], Pre), *ins,
	        bvf->evst->rv[ins->dst_reg]); */

	return err;
}
