#ifndef EVAL_DEFINED_H
#define EVAL_DEFINED_H

#include "../../common/shared.h"
#include "../../common/specs.h"

const char *eval_defined(const struct bpf_reg_val *dst,
	const struct bpf_reg_val *src);

#endif
