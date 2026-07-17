#ifndef SHARED_H
#define SHARED_H

#include <stdint.h>
#include <stddef.h>
#include "fixes.h"

#define _32_BIT_MASK 0x00000000FFFFFFFFULL
#define _64_BIT_MASK 0xFFFFFFFFFFFFFFFFULL

/* Instruction decode (lib/bpf/bpf_def.h): class, source and op selectors
 * plus the ALU opcode set eval_alu dispatches on. */
#define	BPF_CLASS(code)	((code) & 0x07)
#define	BPF_SRC(code)	((code) & 0x08)
#define	BPF_OP(code)	((code) & 0xf0)

#define	BPF_ALU		0x04
#define	EBPF_ALU64	0x07

#define	BPF_K		0x00
#define	BPF_X		0x08

#define	BPF_ADD		0x00
#define	BPF_SUB		0x10
#define	BPF_MUL		0x20
#define	BPF_DIV		0x30
#define	BPF_OR		0x40
#define	BPF_AND		0x50
#define	BPF_LSH		0x60
#define	BPF_RSH		0x70
#define	BPF_NEG		0x80
#define	BPF_MOD		0x90
#define	BPF_XOR		0xa0
#define	EBPF_MOV	0xb0
#define	EBPF_ARSH	0xc0

#define RTE_BPF_ARG_PTR_TYPE(x)	((x) & RTE_BPF_ARG_PTR)

enum rte_bpf_arg_type {
	RTE_BPF_ARG_UNDEF,      /**< undefined */
	RTE_BPF_ARG_RAW,        /**< scalar value */
	RTE_BPF_ARG_PTR = 0x10, /**< pointer to data buffer */
	RTE_BPF_ARG_PTR_MBUF,   /**< pointer to rte_mbuf */
	RTE_BPF_ARG_RESERVED    /**< reserved for internal use */
};

struct rte_bpf_arg {
	enum rte_bpf_arg_type type;
	/**
	 * for ptr type - max size of data buffer it points to
	 * for raw type - the size (in bytes) of the value
	 */
	size_t size;
	size_t buf_size;
	/**< for mbuf ptr type, max size of rte_mbuf data buffer */
};

struct bpf_reg_val {
	struct rte_bpf_arg v;
	uint64_t mask;
	struct {
		int64_t min;
		int64_t max;
	} s;
	struct {
		uint64_t min;
		uint64_t max;
	} u;
};

/* Instruction and evaluation-state shapes for the eval_alu harness
 * (lib/bpf/bpf_def.h / bpf_validate.c). EBPF_REG_NUM is upstream's enum
 * value (EBPF_REG_0 .. EBPF_REG_10, then EBPF_REG_NUM = 11). The 4-bit
 * register fields can encode up to 15, so idx < EBPF_REG_NUM is NOT
 * true by construction: upstream establishes it before eval_alu runs
 * (ins_chk's WRT_REGS/RD_REGS masks reject regs > 10), and the
 * harnesses state that assumption explicitly (eval_alu's idx_ok
 * requires; the BMC drivers' REQUIRE). Only the members eval_alu
 * touches are modelled on bpf_verifier. */
#define	EBPF_REG_NUM	11

struct ebpf_insn {
	uint8_t code;
	uint8_t dst_reg:4;
	uint8_t src_reg:4;
	int16_t off;
	int32_t imm;
};

struct bpf_eval_state {
	struct bpf_reg_val rv[EBPF_REG_NUM];
};

struct bpf_verifier {
	struct bpf_eval_state *evst;
};

#define RTE_MAX(a, b) \
	__extension__ ({ \
		typeof (a) _a_max = (a); \
		typeof (b) _b_max = (b); \
		_a_max > _b_max ? _a_max : _b_max; \
	})

#define RTE_MIN(a, b) \
	__extension__ ({ \
		typeof (a) _a_min = (a); \
		typeof (b) _b_min = (b); \
		_a_min < _b_min ? _a_min : _b_min; \
	})

#define CHAR_BIT  __CHAR_BIT__

#define	RTE_LEN2MASK(ln, tp)	\
	((tp)((uint64_t)-1 >> (sizeof(uint64_t) * CHAR_BIT - (ln))))

#ifdef __FRAMAC__
/*@
	requires v != 0;
	terminates \true;
	assigns \nothing;
	exits \false;

	ensures 0 <= \result <= 63;
	ensures clz_window: (v >> (63 - \result)) == 1;
*/
unsigned int rte_clz64(uint64_t v);
#else
static inline unsigned int rte_clz64(uint64_t v)
{
	return (unsigned int)__builtin_clzll(v);
}
#endif

#endif /* SHARED_H */
