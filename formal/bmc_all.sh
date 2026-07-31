#!/usr/bin/env bash

FAILED=0

CHECKS="
--overflow-check
--unsigned-overflow-check
--ub-shift-check
--memory-leak-check
--nan-check
--struct-fields-check
--data-races-check
--deadlock-check
--lock-order-check
--atomicity-check
"

run_esbmc() {
	esbmc -DALL_FIXES --timeout 300s "$@" || FAILED=1
}

SRCS=$(find harnesses -name '*.c' ! -name '*_main.c' ! -name '*_bmc.c' \
	! -name 'compose_*' ! -name '*_check.c')

for bmc in harnesses/*/*_bmc.c; do
	echo "==== $bmc : default checks ===="
	run_esbmc "$bmc" $SRCS

	for check in $CHECKS; do
		echo "==== $bmc : $check ===="
		run_esbmc "$bmc" $SRCS "$check"
	done
done

AMASK=harnesses/eval_apply_mask/eval_apply_mask_bmc.c
echo "==== $AMASK : -DBMC_WSOUND ===="
run_esbmc -DBMC_WSOUND "$AMASK" $SRCS

echo "==== $AMASK : -DBMC_WIDEN_WITNESS (CONSIST off — E9 must reproduce) ===="
esbmc -DFIX_APPLY_MASK_OPT -DFIX_APPLY_MASK_SIGNED -DBMC_WIDEN_WITNESS \
	--timeout 300s "$AMASK" $SRCS || FAILED=1

exit $FAILED
