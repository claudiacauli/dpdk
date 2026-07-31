#ifndef EVAL_FILL_IMM64_H
#define EVAL_FILL_IMM64_H

#include "../../common/shared.h"
#include "../../common/specs.h"

void eval_fill_imm64(struct bpf_reg_val *rv, uint64_t mask, uint64_t val);

#endif
