#include "../../common/shared.h"
#include "../../common/semantics.h"
#include "../../common/axioms.h"
#include "axioms_exec.h"

/*
 * EXECUTOR-AGREEMENT harness: every ALU case-arm of lib/bpf/bpf_exec.c
 * computes EXACTLY the concrete semantics SEM_* (common/semantics.h)
 * that the validator's soundness/optimality predicates abstract. This
 * is the left arrow of the assurance chain
 *
 *     bpf_exec.c case-arm  ==(agreement, HERE)==  SEM_op
 *     SEM_op image  in-range-of (soundness, eval_*)  abstract intervals
 *
 * whose composition turns per-operator validator soundness into a
 * statement about what DPDK actually executes on the interpreter path.
 * (The JITs are outside this chain: BACKLOG E8 records a CONFIRMED
 * miscompilation in the x86 JIT's shift-by-immediate encoder, found
 * while auditing this campaign's shift preconditions.)
 *
 * FIDELITY. The five op macros below are copied VERBATIM from
 * bpf_exec.c:29-54; each function body is the verbatim case-arm
 * statement. Do not "clean up" either: their point is to be textually
 * the shipped code. The only edit is in BPF_DIV_ZERO_CHECK, where the
 * RTE_BPF_LOG_LINE call is elided (logging is not semantics) and the
 * abort is surfaced as a return value so it is observable in a
 * contract; the CONTROL FLOW is unchanged.
 *
 * CONVENTIONS (see semantics.h for the full rationale):
 *  - registers are arbitrary uint64; 32-bit arms truncate BOTH operands
 *    (the (uint32_t) casts) and zero-extend the result, so 32-bit
 *    theorems apply SEM_* to (operand & _32_BIT_MASK) -- exactly the
 *    masking eval_alu models with eval_apply_mask;
 *  - K-variants materialise the int32 immediate as SEM_FILL(imm, msk),
 *    which is eval_fill_imm's value convention verbatim: sign-extend to
 *    uint64, then mask. At 64 bits that IS sign-extension (imm = -1
 *    becomes 2^64-1); at 32 bits it is plain truncation. Stating all
 *    four variants of every operator is what makes that asymmetry
 *    machine-checked rather than assumed;
 *  - shift counts are NOT masked by the executor, so every shift
 *    theorem is preconditioned on an in-range count. That precondition
 *    is a VALIDATOR OBLIGATION which the validator does NOT currently
 *    discharge (it widens to Top instead) -- BACKLOG E7/E8;
 *  - DIV/MOD X-variants abort the whole program on a zero divisor
 *    (behavior `abort` below); K-variants have no runtime check and
 *    rely on ins_chk's .imm.min = 1 (bpf_validate.c:1723-1734).
 *
 * NOT COVERED HERE (see the campaign classification): the EBPF_END
 * byteswap pair (bpf_exec.c:245-250), whose semantics is host-endianness
 * dependent and goes through the rte_cpu_to_be / rte_cpu_to_le builtins;
 * the validator models it as Top via eval_bele -> eval_max_bound.
 * 32-bit ARSH has no case arm and no ins_chk row (rejected at load on
 * both sides), so there is nothing to state.
 */

/* lib/bpf/bpf_exec.c:29-30, verbatim */
#define BPF_NEG_ALU(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(-(reg)[(ins)->dst_reg]))

/* lib/bpf/bpf_exec.c:32-33, verbatim */
#define EBPF_MOV_ALU_REG(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(reg)[(ins)->src_reg])

/* lib/bpf/bpf_exec.c:35-37, verbatim */
#define BPF_OP_ALU_REG(reg, ins, op, type)	\
	((reg)[(ins)->dst_reg] = \
		(type)(reg)[(ins)->dst_reg] op (type)(reg)[(ins)->src_reg])

/* lib/bpf/bpf_exec.c:39-40, verbatim */
#define EBPF_MOV_ALU_IMM(reg, ins, type)	\
	((reg)[(ins)->dst_reg] = (type)(ins)->imm)

/* lib/bpf/bpf_exec.c:42-44, verbatim */
#define BPF_OP_ALU_IMM(reg, ins, op, type)	\
	((reg)[(ins)->dst_reg] = \
		(type)(reg)[(ins)->dst_reg] op (type)(ins)->imm)

/* lib/bpf/bpf_exec.c:46-54 with the log call elided and the abort made
 * observable as a return value (see FIDELITY above). */
#define BPF_DIV_ZERO_CHECK(reg, ins, type) do { \
	if ((type)(reg)[(ins)->src_reg] == 0) { \
		return 0; \
	} \
} while (0)


/* ================= wrapping arithmetic ================= */

/* case (EBPF_ALU64 | BPF_ADD | BPF_X) -- bpf_exec.c:290 */
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

/* case (EBPF_ALU64 | BPF_ADD | BPF_K) -- bpf_exec.c:253 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_ADD | BPF_X) -- bpf_exec.c:208 */
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

/* case (BPF_ALU | BPF_ADD | BPF_K) -- bpf_exec.c:174 (imm TRUNCATED) */
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

/* case (EBPF_ALU64 | BPF_SUB | BPF_X) -- bpf_exec.c:293 */
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

/* case (EBPF_ALU64 | BPF_SUB | BPF_K) -- bpf_exec.c:256 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_SUB | BPF_X) -- bpf_exec.c:211 */
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

/* case (BPF_ALU | BPF_SUB | BPF_K) -- bpf_exec.c:177 (imm TRUNCATED) */
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

/* case (EBPF_ALU64 | BPF_MUL | BPF_X) -- bpf_exec.c:314 */
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

/* case (EBPF_ALU64 | BPF_MUL | BPF_K) -- bpf_exec.c:277 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_MUL | BPF_X) -- bpf_exec.c:229 */
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

/* case (BPF_ALU | BPF_MUL | BPF_K) -- bpf_exec.c:195 (imm TRUNCATED) */
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

/* case (EBPF_ALU64 | BPF_AND | BPF_X) -- bpf_exec.c:295 */
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

/* case (EBPF_ALU64 | BPF_AND | BPF_K) -- bpf_exec.c:259 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_AND | BPF_X) -- bpf_exec.c:213 */
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

/* case (BPF_ALU | BPF_AND | BPF_K) -- bpf_exec.c:180 (imm TRUNCATED) */
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

/* case (EBPF_ALU64 | BPF_OR | BPF_X) -- bpf_exec.c:298 */
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

/* case (EBPF_ALU64 | BPF_OR | BPF_K) -- bpf_exec.c:262 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_OR | BPF_X) -- bpf_exec.c:216 */
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

/* case (BPF_ALU | BPF_OR | BPF_K) -- bpf_exec.c:183 (imm TRUNCATED) */
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

/* case (EBPF_ALU64 | BPF_XOR | BPF_X) -- bpf_exec.c:310 */
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

/* case (EBPF_ALU64 | BPF_XOR | BPF_K) -- bpf_exec.c:273 (imm SIGN-extended) */
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

/* case (BPF_ALU | BPF_XOR | BPF_X) -- bpf_exec.c:225 */
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

/* case (BPF_ALU | BPF_XOR | BPF_K) -- bpf_exec.c:192 (imm TRUNCATED) */
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


/* ================= shifts (in-range counts; E7/E8) ================= */

/* case (EBPF_ALU64 | BPF_LSH | BPF_X) -- bpf_exec.c:302 */
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

/* case (EBPF_ALU64 | BPF_LSH | BPF_K) -- bpf_exec.c:265 */
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

/* case (BPF_ALU | BPF_LSH | BPF_X) -- bpf_exec.c:220 */
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

/* case (BPF_ALU | BPF_LSH | BPF_K) -- bpf_exec.c:186 */
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

/* case (EBPF_ALU64 | BPF_RSH | BPF_X) -- bpf_exec.c:305 */
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

/* case (EBPF_ALU64 | BPF_RSH | BPF_K) -- bpf_exec.c:268 */
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

/* case (BPF_ALU | BPF_RSH | BPF_X) -- bpf_exec.c:223 */
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

/* case (BPF_ALU | BPF_RSH | BPF_K) -- bpf_exec.c:189 */
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


/* ARSH is ALU64-ONLY: 32-bit ARSH has no case arm in bpf_exec.c and no
 * ins_chk row in bpf_validate.c -- rejected at load on both sides.
 * SEM_ARSH is the SIGNED image (semantics.h); the register receives its
 * re-encoding, which is exactly eval_arsh's unsigned image term. */

/* case (EBPF_ALU64 | EBPF_ARSH | BPF_X) -- bpf_exec.c:308 */
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

/* case (EBPF_ALU64 | EBPF_ARSH | BPF_K) -- bpf_exec.c:271 */
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


/* ================= negation ================= */

/* case (EBPF_ALU64 | BPF_NEG) -- bpf_exec.c:328 (negate uncast, then cast) */
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

/* case (BPF_ALU | BPF_NEG) -- bpf_exec.c:243 (negate-then-truncate == truncate-then-negate) */
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


/* ================= move / materialise ================= */

/* case (EBPF_ALU64 | EBPF_MOV | BPF_X) -- bpf_exec.c:325 */
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

/* case (EBPF_ALU64 | EBPF_MOV | BPF_K) -- bpf_exec.c:286 (SIGN-extends) */
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

/* case (BPF_ALU | EBPF_MOV | BPF_X) -- bpf_exec.c:240 */
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

/* case (BPF_ALU | EBPF_MOV | BPF_K) -- bpf_exec.c:204 (ZERO-extends) */
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


/* ================= division =================
 * X-variants: BPF_DIV_ZERO_CHECK aborts the whole program (returns 0)
 * BEFORE computing, so the two behaviors are stated explicitly. Note
 * the 32-bit check tests only the LOW 32 BITS of the divisor: a source
 * register holding 2^32 aborts even though it is nonzero.
 * K-variants: no runtime check at all -- the requires below is a
 * VALIDATOR obligation, discharged by ins_chk's .imm.min = 1.
 */

/* case (EBPF_ALU64 | BPF_DIV | BPF_X) -- bpf_exec.c:318 */
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

/* case (BPF_ALU | BPF_DIV | BPF_X) -- bpf_exec.c:233 (check tests LOW 32 BITS) */
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

/* case (EBPF_ALU64 | BPF_DIV | BPF_K) -- bpf_exec.c:280 (no runtime check) */
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

/* case (BPF_ALU | BPF_DIV | BPF_K) -- bpf_exec.c:198 (no runtime check) */
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

/* case (EBPF_ALU64 | BPF_MOD | BPF_X) -- bpf_exec.c:322 */
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

/* case (BPF_ALU | BPF_MOD | BPF_X) -- bpf_exec.c:237 (check tests LOW 32 BITS) */
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

/* case (EBPF_ALU64 | BPF_MOD | BPF_K) -- bpf_exec.c:283 (no runtime check) */
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

/* case (BPF_ALU | BPF_MOD | BPF_K) -- bpf_exec.c:201 (no runtime check) */
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
