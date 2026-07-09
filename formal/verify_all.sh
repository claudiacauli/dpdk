#!/usr/bin/env bash


FAILED=0

run_wp() {
	frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 "$@" || FAILED=1
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

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 20 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 120 \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

exit $FAILED
