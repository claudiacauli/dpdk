#ifndef LEMMAS_DELIVER_H
#define LEMMAS_DELIVER_H

#include "eval_alu.h"
#include "../eval_apply_mask/eval_apply_mask.h"
#include "../eval_and/eval_and.h"
#include "../eval_or/eval_or.h"
#include "../eval_xor/eval_xor.h"
#include "../../common/axioms_or.h"
#include "../eval_xor/axioms_xor.h"
#include "../eval_add/eval_add.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_mul/eval_mul.h"
#include "../eval_divmod/eval_divmod.h"
#include "../eval_neg/eval_neg.h"
#include "../eval_arsh/eval_arsh.h"
#include "../eval_lsh/eval_lsh.h"
#include "../eval_rsh/eval_rsh.h"

/*@

lemma sext_remask_3232:
	\forall integer x; 0 <= x <= 0xFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFF)) & 0xFFFFFFFF) == (x & 0xFFFFFFFF);

lemma sext_remask_6464:
	\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFFFFFFFFFF)) & 0xFFFFFFFFFFFFFFFF)
		== (x & 0xFFFFFFFFFFFFFFFF);

lemma sext_remask_6432:
	\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFFFFFFFFFF)) & 0xFFFFFFFF)
		== (x & 0xFFFFFFFF);

lemma wit_covers_from_apply_mask:
	\forall struct bpf_reg_val od, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(od.mask == 0xFFFFFFFF || od.mask == 0xFFFFFFFFFFFFFFFF) &&
		eval_apply_mask_unsigned_soundness(od, nw, msk) &&
		eval_apply_mask_signed_soundness(od, nw, msk)
		==> alu_wit_covers(od, nw, msk);

lemma alu_compose_mov_u:
	\forall struct bpf_reg_val od, os, md, ms;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_MOV &&
		alu_compose_pre(od, os, md, ms, ins, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, ms);

lemma alu_compose_mov_s:
	\forall struct bpf_reg_val od, os, md, ms;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_MOV &&
		alu_compose_pre(od, os, md, ms, ins, msk)
		==> eval_alu_signed_soundness(od, os, ins, ms);

lemma wit_covers_congr:
	\forall struct bpf_reg_val a, b, nw; \forall uint64_t msk;
		a.mask == b.mask &&
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_wit_covers(a, nw, msk)
		==> alu_wit_covers(b, nw, msk);

lemma wit_covers_congr2:
	\forall struct bpf_reg_val od, a, b; \forall uint64_t msk;
		a.mask == b.mask &&
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_wit_covers(od, a, msk)
		==> alu_wit_covers(od, b, msk);

lemma imm_covers_congr:
	\forall struct bpf_reg_val a, b; \forall struct ebpf_insn ins;
	\forall uint64_t msk;
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_imm_covers(a, ins, msk)
		==> alu_imm_covers(b, ins, msk);

lemma lor_strip_32:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
	==> ((a | b) & 0xFFFFFFFF) == (a | b);

lemma lor_strip_64:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
	==> ((a | b) & 0xFFFFFFFFFFFFFFFF) == (a | b);

lemma lxor_strip_32:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
	==> ((a ^ b) & 0xFFFFFFFF) == (a ^ b);

lemma lxor_strip_64:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
	==> ((a ^ b) & 0xFFFFFFFFFFFFFFFF) == (a ^ b);

lemma alu_compose_add_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_ADD &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_add_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_sub_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_SUB &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_sub_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_mul_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_MUL &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_mul_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_divmod_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		(BPF_OP(ins.code) == BPF_DIV ||
		 BPF_OP(ins.code) == BPF_MOD) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_divmod_signed_soundness(BPF_OP(ins.code), md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_and_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_AND &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_and_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_or_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_OR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_or_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_xor_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_XOR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_xor_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_arsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_ARSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_arsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_neg_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_NEG &&
		msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
		alu_wit_covers(od, md, msk) &&
		eval_neg_signed_soundness(md, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_selfxor_s:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.s.min == 0 && nw.s.max == 0
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_selfxor_u_cover:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.u.min <= 0 <= nw.u.max
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_selfxor_s_cover:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.s.min <= 0 <= nw.s.max
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma cast_land_strip:
	\forall integer x; \forall uint64_t m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) && 0 <= x
	==> (((uint64_t)(x & m)) & m) == (x & m);

lemma strip_cast_land_under_lsl_32:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) << q) & m) == ((((x & m)) << q) & m);

lemma strip_cast_land_under_lsl_64:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFFFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) << q) & m) == ((((x & m)) << q) & m);

lemma strip_cast_land_under_lsr_32:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) >> q)) == (((x & m)) >> q);

lemma strip_cast_land_under_lsr_64:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFFFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) >> q)) == (((x & m)) >> q);

predicate lsh_dpat_ssound(struct bpf_reg_val md, struct bpf_reg_val ms,
                          struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		0 <= x && 0 <= y &&
		un_witness(md, x & msk, msk) && un_witness(ms, y & msk, msk) &&
		(y & msk) < op_bits(msk)
			==> nw.s.min <= to_signed((((x & msk) << (y & msk)) & msk), msk)
			    <= nw.s.max;

predicate rsh_dpat_ssound(struct bpf_reg_val md, struct bpf_reg_val ms,
                          struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		0 <= x && 0 <= y &&
		un_witness(md, x & msk, msk) && un_witness(ms, y & msk, msk) &&
		(y & msk) < op_bits(msk)
			==> nw.s.min <= to_signed(((x & msk) >> (y & msk)), msk)
			    <= nw.s.max;

lemma lsh_dadapt:
	\forall struct bpf_reg_val md, ms, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	eval_lsh_signed_soundness(md, ms, nw, msk)
	==> lsh_dpat_ssound(md, ms, nw, msk);

lemma rsh_dadapt:
	\forall struct bpf_reg_val md, ms, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	eval_rsh_signed_soundness(md, ms, nw, msk)
	==> rsh_dpat_ssound(md, ms, nw, msk);

lemma alu_compose_lsh_s_dpat:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		lsh_dpat_ssound(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_rsh_s_dpat:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		rsh_dpat_ssound(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_lsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_lsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_rsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_rsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);
*/

#endif
