#!/usr/bin/env bash
#
# eval_mul BMC — run on a big box (the 64-bit symbolic multiply blows up
# bit-vector solvers; a laptop times out, 96 cores + 1TB RAM does not).
#
# Splits the soundness check into (track x width) cells so each solver
# query carries the fewest symbolic multiplies, and runs the cells in
# parallel. Prints one PASS/FAIL/TIMEOUT line per cell.
#
# Expected results:
#   FIXED cells        -> all SUCCESSFUL (the soundness result)
#   ORIGINAL cells     -> FAILED (each is a witnessed upstream bug)
#   SANITY             -> FAILED (asserts reachable; harness not vacuous)
#
# Usage:  ./bmc_mul.sh [timeout_seconds]   (default 1200)

cd "$(dirname "$0")" || exit 1
TMO=${1:-1200}
SR="harnesses/eval_mul/eval_mul.c harnesses/eval_umax_bound/eval_umax_bound.c harnesses/eval_smax_bound/eval_smax_bound.c"
BMC=harnesses/eval_mul/eval_mul_bmc.c
OUT=$(mktemp -d)

# ESBMC's bundled clang can't find the system <stddef.h> on Linux
# (its wrapper does #include_next with nothing to chain to). Add the
# compiler's internal header dir so include_next resolves. Harmless on
# macOS where the headers are already found.
SYSINC=
for d in "$(gcc -print-file-name=include 2>/dev/null)" \
         "$(clang -print-resource-dir 2>/dev/null)/include"; do
	[ -n "$d" ] && [ -f "$d/stddef.h" ] && SYSINC="$SYSINC -I$d"
done

cell() { # label  defs...
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

echo "=== FIXED (expect all PASS) — soundness of the corrected eval_mul ==="
cell fixed-u32  -DALL_FIXES -DBMC_U_ONLY -DBMC_32 &
cell fixed-s32  -DALL_FIXES -DBMC_S_ONLY -DBMC_32 &
cell fixed-u64  -DALL_FIXES -DBMC_U_ONLY          &
cell fixed-s64  -DALL_FIXES -DBMC_S_ONLY          &
wait

echo
echo "=== ORIGINAL (expect FAIL — each is a witnessed upstream bug) ==="
# U1 lives at 64-bit (msk>>opsz UB); S1 at 32-bit (no sign-ext); S2 both.
cell orig-u64   -DBMC_U_ONLY          &   # U1: unsigned overflow guard
cell orig-s32   -DBMC_S_ONLY -DBMC_32 &   # S1: signed-const sign extension
cell orig-s64   -DBMC_S_ONLY          &   # S2: signed non-const overflow
wait

echo
echo "=== SANITY (expect FAIL — proves the asserts are reachable) ==="
cell sanity-u32 -DALL_FIXES -DBMC_U_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-s32 -DALL_FIXES -DBMC_S_ONLY -DBMC_32 -DBMC_SANITY &
wait

echo
echo "counterexample traces (if any) are under: $OUT"
