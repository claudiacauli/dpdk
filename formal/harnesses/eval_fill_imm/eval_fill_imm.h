#ifndef EVAL_FILL_IMM_H
#define EVAL_FILL_IMM_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*
 * eval_fill_imm materialises an immediate operand as a constant RAW
 * register: both tracks pin the single value. The unsigned track holds
 * the w-bit PATTERN (uint64)imm & mask; the signed track must hold its
 * CANONICAL (sign-extended) reading to_signed(pattern, mask) — the
 * output is a constant, so the contract is exact and needs no
 * quantified soundness predicates.
 */

void eval_fill_imm(struct bpf_reg_val *rv, uint64_t mask, int32_t imm);

#endif /* EVAL_FILL_IMM_H */
