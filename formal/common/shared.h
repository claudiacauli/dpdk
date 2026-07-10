#ifndef SHARED_H
#define SHARED_H

#include <stdint.h>
#include <stddef.h>
#include "fixes.h"

#define _32_BIT_MASK 0x00000000FFFFFFFFULL
#define _64_BIT_MASK 0xFFFFFFFFFFFFFFFFULL

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

#endif /* SHARED_H */
