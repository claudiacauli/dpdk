#!/usr/bin/env bash
#
# eval_divmod BMC — the symbolic 64-bit udiv/urem circuits are heavy for
# bit-vector solvers (same profile as eval_mul's multiplies); run on a big
# box if the laptop cells time out.
#
# Splits the check into (op x width) cells so each solver query carries a
# single symbolic divider, and runs the cells in parallel. Prints one
# PASS/FAIL/TIMEOUT line per cell.
#
# Expected results:
#   FIXED cells     -> all SUCCESSFUL (the soundness result)
#   ORIGINAL 32-bit -> FAILED (S1: raw patterns stored as signed bounds —
#                      the sign-contiguity test uses INT64 boundaries
#                      regardless of msk; witnessed instantly)
#   ORIGINAL 64-bit -> SUCCESSFUL (the bug is 32-bit-only; the 64-bit
#                      reinterpretation coincides with the fix)
#   SANITY          -> FAILED (asserts reachable; harness not vacuous)
#
# Usage:  ./bmc_divmod.sh [timeout_seconds]   (default 1200)

cd "$(dirname "$0")" || exit 1
TMO=${1:-1200}
SR="harnesses/eval_divmod/eval_divmod.c harnesses/eval_smax_bound/eval_smax_bound.c"
BMC=harnesses/eval_divmod/eval_divmod_bmc.c
OUT=$(mktemp -d)

# ESBMC's bundled clang can't find the system <stddef.h> on some Linux
# setups (its wrapper does #include_next with nothing to chain to); there,
# add the compiler's internal header dir so include_next resolves. Do it
# ONLY when actually needed: on macOS injecting clang's resource dir
# BREAKS the chain instead (stdint.h resolves to the injected copy, whose
# #include_next then finds nothing), so probe first.
SYSINC=
PROBE=$(mktemp -t esbmc_probe).c
printf '#include <stdint.h>\nint main(void){uint64_t x=0;return (int)x;}\n' >"$PROBE"
if ! esbmc "$PROBE" >/dev/null 2>&1; then
	for d in "$(gcc -print-file-name=include 2>/dev/null)" \
	         "$(clang -print-resource-dir 2>/dev/null)/include"; do
		[ -n "$d" ] && [ -f "$d/stddef.h" ] && SYSINC="$SYSINC -I$d"
	done
fi
rm -f "$PROBE"

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

echo "=== FIXED (expect all PASS) — soundness of the corrected eval_divmod ==="
cell fixed-div32 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_32 &
cell fixed-mod32 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_32 &
cell fixed-div64 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_64 &
cell fixed-mod64 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_64 &
wait

echo
echo "=== ORIGINAL (expect 32-bit FAIL = the witnessed bug; 64-bit PASS) ==="
cell orig-div32  -DBMC_DIV_ONLY -DBMC_32 &   # S1: signed-32 reinterpretation
cell orig-mod32  -DBMC_MOD_ONLY -DBMC_32 &   # S1 via the mod path
cell orig-div64  -DBMC_DIV_ONLY -DBMC_64 &   # 64-bit path is correct
cell orig-mod64  -DBMC_MOD_ONLY -DBMC_64 &
wait

echo
echo "=== SANITY (expect FAIL — proves the asserts are reachable) ==="
cell sanity-div32 -DALL_FIXES -DBMC_DIV_ONLY -DBMC_32 -DBMC_SANITY &
cell sanity-mod64 -DALL_FIXES -DBMC_MOD_ONLY -DBMC_64 -DBMC_SANITY &
wait

echo
echo "counterexample traces (if any) are under: $OUT"
