#include "../../common/shared.h"
#include "../../common/semantics.h"
#include "../../common/axioms.h"
#include "axioms_exec.h"

#define BPF_NEG_ALU(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(-(reg)[(ins)->dst_reg]))

#define EBPF_MOV_ALU_REG(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(reg)[(ins)->src_reg])

#define BPF_OP_ALU_REG(reg, ins, op, type)	\
	((reg)[(ins)->dst_reg] = \
		(type)(reg)[(ins)->dst_reg] op (type)(reg)[(ins)->src_reg])

#define EBPF_MOV_ALU_IMM(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(ins)->imm)

#define BPF_OP_ALU_IMM(reg, ins, op, type)	\
	((reg)[(ins)->dst_reg] = \
		(type)(reg)[(ins)->dst_reg] op (type)(ins)->imm)

#define BPF_DIV_ZERO_CHECK(reg, ins, type) do { \
	if ((type)(reg)[(ins)->src_reg] == 0) { \
		return 0; \
	} \
} while (0)

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_ADD(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_add_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, +, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_ADD(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_add_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, +, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_ADD((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_add_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, +, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_ADD((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_add_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, +, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_SUB(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_sub_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, -, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_SUB(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_sub_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, -, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_SUB((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_sub_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, -, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_SUB((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_sub_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, -, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MUL(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_mul_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, *, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MUL(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_mul_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, *, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MUL((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_mul_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, *, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MUL((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_mul_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, *, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_AND(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_and_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, &, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_AND(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_and_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, &, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_AND((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_and_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, &, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_AND((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_and_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, &, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_OR(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_or_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, |, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_OR(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_or_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, |, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_OR((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_or_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, |, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_OR((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_or_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, |, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_XOR(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_xor_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, ^, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_XOR(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK), _64_BIT_MASK);
*/
void exec_alu64_xor_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, ^, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_XOR((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_xor_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, ^, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_XOR((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_xor_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, ^, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	requires reg[ins->src_reg] < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_LSH(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_lsh_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, <<, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires 0 <= ins->imm < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_LSH(\old(reg[ins->dst_reg]), ins->imm, _64_BIT_MASK);
*/
void exec_alu64_lsh_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, <<, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	requires (reg[ins->src_reg] & _32_BIT_MASK) < 32;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_LSH((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_lsh_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, <<, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires 0 <= ins->imm < 32;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_LSH((\old(reg[ins->dst_reg]) & _32_BIT_MASK), ins->imm, _32_BIT_MASK);
*/
void exec_alu32_lsh_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, <<, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	requires reg[ins->src_reg] < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_RSH(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_rsh_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, >>, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires 0 <= ins->imm < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_RSH(\old(reg[ins->dst_reg]), ins->imm, _64_BIT_MASK);
*/
void exec_alu64_rsh_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, >>, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	requires (reg[ins->src_reg] & _32_BIT_MASK) < 32;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_RSH((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_rsh_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, >>, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires 0 <= ins->imm < 32;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_RSH((\old(reg[ins->dst_reg]) & _32_BIT_MASK), ins->imm, _32_BIT_MASK);
*/
void exec_alu32_rsh_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, >>, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	requires reg[ins->src_reg] < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		(((uint64_t)SEM_ARSH(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]), _64_BIT_MASK)) & _64_BIT_MASK);
*/
void exec_alu64_arsh_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_REG(reg, ins, >>, int64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires 0 <= ins->imm < 64;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		(((uint64_t)SEM_ARSH(\old(reg[ins->dst_reg]), ins->imm, _64_BIT_MASK)) & _64_BIT_MASK);
*/
void exec_alu64_arsh_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, >>, int64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_NEG(\old(reg[ins->dst_reg]), _64_BIT_MASK);
*/
void exec_alu64_neg(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_NEG_ALU(reg, ins, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_NEG((\old(reg[ins->dst_reg]) & _32_BIT_MASK), _32_BIT_MASK);
*/
void exec_alu32_neg(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_NEG_ALU(reg, ins, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MASK(\old(reg[ins->src_reg]), _64_BIT_MASK);
*/
void exec_alu64_mov_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	EBPF_MOV_ALU_REG(reg, ins, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_FILL(ins->imm, _64_BIT_MASK);
*/
void exec_alu64_mov_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	EBPF_MOV_ALU_IMM(reg, ins, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MASK(\old(reg[ins->src_reg]), _32_BIT_MASK);
*/
void exec_alu32_mov_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	EBPF_MOV_ALU_REG(reg, ins, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_FILL(ins->imm, _32_BIT_MASK);
*/
void exec_alu32_mov_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	EBPF_MOV_ALU_IMM(reg, ins, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	behavior abort:
		assumes reg[ins->src_reg] == 0;
		ensures \result == 0;
		ensures frame: reg[ins->dst_reg] == \old(reg[ins->dst_reg]);
	behavior compute:
		assumes reg[ins->src_reg] != 0;
		ensures agree: reg[ins->dst_reg] == SEM_DIV(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]));
	complete behaviors;
	disjoint behaviors;
*/
uint64_t exec_alu64_div_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_DIV_ZERO_CHECK(reg, ins, uint64_t);
	BPF_OP_ALU_REG(reg, ins, /, uint64_t);
	return 1;
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	behavior abort:
		assumes (reg[ins->src_reg] & _32_BIT_MASK) == 0;
		ensures \result == 0;
		ensures frame: reg[ins->dst_reg] == \old(reg[ins->dst_reg]);
	behavior compute:
		assumes (reg[ins->src_reg] & _32_BIT_MASK) != 0;
		ensures agree: reg[ins->dst_reg] == SEM_DIV((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK));
	complete behaviors;
	disjoint behaviors;
*/
uint64_t exec_alu32_div_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_DIV_ZERO_CHECK(reg, ins, uint32_t);
	BPF_OP_ALU_REG(reg, ins, /, uint32_t);
	return 1;
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires SEM_FILL(ins->imm, _64_BIT_MASK) != 0;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_DIV(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK));
*/
void exec_alu64_div_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, /, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires SEM_FILL(ins->imm, _32_BIT_MASK) != 0;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_DIV((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK));
*/
void exec_alu32_div_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, /, uint32_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	behavior abort:
		assumes reg[ins->src_reg] == 0;
		ensures \result == 0;
		ensures frame: reg[ins->dst_reg] == \old(reg[ins->dst_reg]);
	behavior compute:
		assumes reg[ins->src_reg] != 0;
		ensures agree: reg[ins->dst_reg] == SEM_MOD(\old(reg[ins->dst_reg]), \old(reg[ins->src_reg]));
	complete behaviors;
	disjoint behaviors;
*/
uint64_t exec_alu64_mod_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_DIV_ZERO_CHECK(reg, ins, uint64_t);
	BPF_OP_ALU_REG(reg, ins, %, uint64_t);
	return 1;
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires ins->src_reg < EBPF_REG_NUM;
	terminates \true;
	assigns reg[ins->dst_reg];

	behavior abort:
		assumes (reg[ins->src_reg] & _32_BIT_MASK) == 0;
		ensures \result == 0;
		ensures frame: reg[ins->dst_reg] == \old(reg[ins->dst_reg]);
	behavior compute:
		assumes (reg[ins->src_reg] & _32_BIT_MASK) != 0;
		ensures agree: reg[ins->dst_reg] == SEM_MOD((\old(reg[ins->dst_reg]) & _32_BIT_MASK), (\old(reg[ins->src_reg]) & _32_BIT_MASK));
	complete behaviors;
	disjoint behaviors;
*/
uint64_t exec_alu32_mod_x(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_DIV_ZERO_CHECK(reg, ins, uint32_t);
	BPF_OP_ALU_REG(reg, ins, %, uint32_t);
	return 1;
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires SEM_FILL(ins->imm, _64_BIT_MASK) != 0;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MOD(\old(reg[ins->dst_reg]), SEM_FILL(ins->imm, _64_BIT_MASK));
*/
void exec_alu64_mod_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, %, uint64_t);
}

/*@
	requires \valid(reg + (0 .. EBPF_REG_NUM - 1));
	requires \valid_read(ins);
	requires \separated(reg + (0 .. EBPF_REG_NUM - 1), ins);
	requires ins->dst_reg < EBPF_REG_NUM;
	requires SEM_FILL(ins->imm, _32_BIT_MASK) != 0;
	terminates \true;
	assigns reg[ins->dst_reg];

	ensures agree: reg[ins->dst_reg] ==
		SEM_MOD((\old(reg[ins->dst_reg]) & _32_BIT_MASK), SEM_FILL(ins->imm, _32_BIT_MASK));
*/
void exec_alu32_mod_k(uint64_t reg[EBPF_REG_NUM], const struct ebpf_insn *ins)
{
	BPF_OP_ALU_IMM(reg, ins, %, uint32_t);
}
