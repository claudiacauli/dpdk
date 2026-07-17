#!/usr/bin/env bash
#
# Build and run tests/tests.c against the REAL validator code, both
# unfixed (faithful upstream) and fixed (-DALL_FIXES). The eval_* .c files
# compile as plain C — the ACSL proof annotations are comments — so this
# runs the actual range-tracking logic.
#
# Usage:
#   ./tests/run_tests.sh            # both builds
#   ./tests/run_tests.sh nofix      # only the unfixed build
#   ./tests/run_tests.sh fix        # only the fixed build
#   CC=clang ./tests/run_tests.sh   # pick a compiler
#
# To try a single fix instead of all, edit FIX below or run cc by hand
# with e.g. -DFIX_APPLY_MASK_CONSIST (see common/fixes.h for the list).

cd "$(dirname "$0")/.." || exit 1        # -> formal/

# gnu11, not c11: shared.h's RTE_MAX/RTE_MIN use typeof + statement
# expressions (GNU extensions), exactly as the real DPDK headers do.
CC=${CC:-cc}
FLAGS="-std=gnu11 -Wall -Wno-unused-function -Wno-unused-variable"

# Every operator/dispatcher implementation; the mains and BMC drivers
# (which carry their own main()) are excluded.
CORE=$(find harnesses -name '*.c' ! -name '*_main.c' ! -name '*_bmc.c')

OUT=$(mktemp -d)
WHICH=${1:-both}

build_run() { # <label> <extra-cflags>
	local label=$1 extra=$2 bin="$OUT/t_$1"
	echo "############################################################"
	echo "#  $label"
	echo "############################################################"
	if $CC $FLAGS $extra tests/tests.c $CORE -o "$bin"; then
		"$bin"
	else
		echo "BUILD FAILED ($label)"
		return 1
	fi
	echo
}

[ "$WHICH" = both ] || [ "$WHICH" = nofix ] && \
	build_run "NO FIXES (upstream)" ""
[ "$WHICH" = both ] || [ "$WHICH" = fix ] && \
	build_run "ALL FIXES" "-DALL_FIXES"
