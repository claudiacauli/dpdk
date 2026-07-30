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
#
# compose_* and *_check.c are WP-only translation units: the compose_*
# files are the Phase B/C proof-engineering record (ACSL lemma blocks
# plus, in compose_deliver2.c, a SECOND definition of eval_alu that
# predates the merge into eval_alu.c), and the *_check.c files are
# one-line @lemma drivers. None of them contributes anything ESBMC can
# execute, and compose_deliver2.c would put a duplicate eval_alu in the
# link. Excluded so this glob cannot pick up a stale dispatcher.
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

# Flag-gated legs. These are invisible to the loop above (which passes only
# -DALL_FIXES), so without these lines they never execute: BMC_WSOUND sat
# unrun from the day it was written until 2026-07-30, and the assertions it
# guards had drifted out of sync with the contract of record meanwhile.
#   wsound        witness transport across masking, under width_fits
#   widen_witness candidate defect #9, deterministic (review_04 §4.1)
AMASK=harnesses/eval_apply_mask/eval_apply_mask_bmc.c
for leg in BMC_WSOUND BMC_WIDEN_WITNESS; do
	echo "==== $AMASK : -D$leg ===="
	run_esbmc "-D$leg" "$AMASK" $SRCS
done

exit $FAILED
