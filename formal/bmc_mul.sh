#!/usr/bin/env bash

cd "$(dirname "$0")" || exit 1
TMO=${1:-1200}
SR="harnesses/eval_mul/eval_mul.c harnesses/eval_umax_bound/eval_umax_bound.c harnesses/eval_smax_bound/eval_smax_bound.c"
BMC=harnesses/eval_mul/eval_mul_bmc.c
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

echo "=== FIXED (expect all PASS) — intersection soundness of eval_mul ==="
cell fixed-u32  -DALL_FIXES -DBMC_U_ONLY -DBMC_32 &
cell fixed-s32  -DALL_FIXES -DBMC_S_ONLY -DBMC_32 &
cell fixed-u64  -DALL_FIXES -DBMC_U_ONLY -DBMC_64 &
cell fixed-s64  -DALL_FIXES -DBMC_S_ONLY -DBMC_64 &
wait

echo
echo "=== SANITY (expect FAIL — proves the asserts are reachable) ==="
cell sanity-u32 -DALL_FIXES -DBMC_U_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-s32 -DALL_FIXES -DBMC_S_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-u64 -DALL_FIXES -DBMC_U_ONLY -DBMC_64 -DBMC_SANITY &
cell sanity-s64 -DALL_FIXES -DBMC_S_ONLY -DBMC_64 -DBMC_SANITY &
wait

echo
echo "counterexample traces (if any) are under: $OUT"
