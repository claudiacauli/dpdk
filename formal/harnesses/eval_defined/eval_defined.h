#ifndef EVAL_DEFINED_H
#define EVAL_DEFINED_H

#include "../../common/shared.h"
#include "../../common/specs.h"

/*
 * eval_defined rejects instructions whose (nullable) operands are in
 * UNDEF state. The contract is an exact iff: an error is returned
 * precisely when a non-null operand is UNDEF. Upstream it is called
 * from the ALU, jump, store and call evaluators — hence its own
 * harness folder rather than a static helper of eval_alu.
 */

const char *eval_defined(const struct bpf_reg_val *dst,
	const struct bpf_reg_val *src);

#endif /* EVAL_DEFINED_H */
