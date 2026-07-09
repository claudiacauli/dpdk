#ifndef EVAL_APPLY_MASK_H
#define EVAL_APPLY_MASK_H

#include "../../common/shared.h"
#include "../../common/specs.h"

void eval_apply_mask(struct bpf_reg_val *rv, uint64_t mask);

#endif
