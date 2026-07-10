#!/usr/bin/env bash


FAILED=0

# Parallel prover tasks: one per PHYSICAL core by default; override with
# WP_PAR=n. Logical (SMT/hyperthread) counts oversubscribe the ALUs and
# slow every prover down — bad for goals near their timeout ceiling. Only
# helps passes with many goals — a single isolated goal is still one
# single-threaded prover, whatever the machine.
phys_cores() {
	if command -v lscpu >/dev/null 2>&1; then
		# unique (core, socket) pairs among online CPUs
		lscpu -b -p=Core,Socket | grep -v '^#' | sort -u | wc -l
	else
		sysctl -n hw.physicalcpu 2>/dev/null || nproc 2>/dev/null || echo 4
	fi
}
NPAR=${WP_PAR:-$(phys_cores)}

run_wp() {
	frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-par "$NPAR" "$@" || FAILED=1
}

contract_has() {
	local prop=$1 f
	shift
	for f in "$@"; do
		case "$f" in
		*.c|*.h)
			grep -Eq "ensures[[:space:]]+$prop[[:space:]]*:" "$f" && return 0
			;;
		esac
	done
	return 1
}

verify() {
	run_wp "$@" -wp-prop=-usound,-ssound
	local prop
	for prop in usound ssound; do
		if contract_has "$prop" "$@"; then
			run_wp "$@" -wp-prop "$prop"
		fi
	done
}

verify -wp-timeout 20 \
	-wp-fct eval_umax_bound \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_smax_bound \
	harnesses/eval_smax_bound/eval_smax_bound_main.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_max_bound \
	harnesses/eval_max_bound/eval_max_bound_main.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_fill_max_bound \
	harnesses/eval_fill_max_bound/eval_fill_max_bound_main.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 \
	-wp-fct eval_sub \
	harnesses/eval_sub/eval_sub_main.c \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

exit $FAILED
