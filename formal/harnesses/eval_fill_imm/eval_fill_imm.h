#ifndef EVAL_FILL_IMM_H
#define EVAL_FILL_IMM_H

#include "../../common/shared.h"
#include "../../common/specs.h"

void eval_fill_imm(struct bpf_reg_val *rv, uint64_t mask, int32_t imm);

#endif
