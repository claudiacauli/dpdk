#!/usr/bin/env bash

FAILED=0

# One run per check: a violated property ends a run, so batching checks
# would mask later ones. The default run (no flag) covers array bounds,
# pointer safety, division by zero and the harness assertions. Note that
# the eval_* interval arithmetic wraps unsigned integers BY DESIGN, so
# --unsigned-overflow-check is expected to flag those operations.
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

# Link every harness implementation into every run (mains and other BMC
# drivers excluded); ESBMC slices away whatever the driver doesn't reach.
SRCS=$(find harnesses -name '*.c' ! -name '*_main.c' ! -name '*_bmc.c')

for bmc in harnesses/*/*_bmc.c; do
	echo "==== $bmc : default checks ===="
	run_esbmc "$bmc" $SRCS

	for check in $CHECKS; do
		echo "==== $bmc : $check ===="
		run_esbmc "$bmc" $SRCS "$check"
	done
done

exit $FAILED
