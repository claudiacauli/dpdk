#ifndef EVAL_FILL_IMM64_H
#define EVAL_FILL_IMM64_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*
 * eval_fill_imm64 pins *rv to the single w-bit pattern val (val <= mask):
 * the unsigned track holds the pattern, the signed track its canonical
 * (sign-extended) reading. It is the exact-constant primitive under
 * eval_fill_imm and, upstream, the LDDW / call / stack paths. It does
 * NOT touch rv->v (type/size): callers set the type themselves.
 */

void eval_fill_imm64(struct bpf_reg_val *rv, uint64_t mask, uint64_t val);

#endif /* EVAL_FILL_IMM64_H */
