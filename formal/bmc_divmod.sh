#!/usr/bin/env bash

cd "$(dirname "$0")" || exit 1
TMO=${1:-1200}
SR="harnesses/eval_divmod/eval_divmod.c harnesses/eval_smax_bound/eval_smax_bound.c"
BMC=harnesses/eval_divmod/eval_divmod_bmc.c
OUT=$(mktemp -d)

SYSINC=
GCC_INC=$(gcc -print-file-name=include 2>/dev/null)
[ -f "$GCC_INC/stddef.h" ] && SYSINC="-I$GCC_INC"

cell() {
	local label=$1; shift
	local f="$OUT/$label"
	esbmc "$@" $SYSINC --timeout "${TMO}s" $BMC $SR >"$f" 2>&1
	local v
	if   grep -q "VERIFICATION SUCCESSFUL" "$f"; then v="PASS"
	elif grep -q "VERIFICATION FAILED"     "$f"; then v="FAIL"
	elif grep -qi "Timed out"              "$f"; then v="TIMEOUT"
	elif grep -qi "ERROR"                  "$f"; then v="ERROR(see file)"
	else v="???"; fi
	printf '%-28s %s\n' "$label" "$v"
}

echo "=== FIXED (expect all PASS) — intersection soundness of eval_divmod ==="
cell fixed-div32 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_32 &
cell fixed-mod32 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_32 &
cell fixed-div64 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_64 &
cell fixed-mod64 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_64 &
wait

echo
echo "=== SANITY (expect FAIL — proves the asserts are reachable) ==="
cell sanity-div32 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-mod32 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-div64 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_64 -DBMC_SANITY &
cell sanity-mod64 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_64 -DBMC_SANITY &
wait

echo
echo "counterexample traces (if any) are under: $OUT"
