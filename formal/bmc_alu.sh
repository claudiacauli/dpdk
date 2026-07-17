#!/usr/bin/env bash
#
# eval_alu BMC — the monolithic dispatcher harness is intractable for
# bit-vector solvers even restricted to the linear ops (>30min on an
# M-series laptop: every reachable operator circuit plus the 11-slot
# symbolic register file lands in one query). Split into (op x width)
# cells so each query carries a single operator circuit, and run the
# cells in parallel. Prints one PASS/FAIL/TIMEOUT line per cell.
# The mul/div/mod/shift cells inherit the eval_mul / eval_divmod solver
# profile — run on a big box if the laptop cells time out.
#
# Expected results:
#   FIXED cells -> all SUCCESSFUL (the dispatcher glue result: frame,
#                  error semantics, register invariant at the op width)
#   SANITY      -> FAILED (asserts reachable; harness not vacuous)
#
# Unfixed-original witnesses are NOT run at this level: each upstream
# bug is witnessed precisely by its own operator's BMC cells (see
# bmc_divmod.sh and the per-harness *_bmc.c gates).
#
# Usage:  ./bmc_alu.sh [timeout_seconds]   (default 1200)

cd "$(dirname "$0")" || exit 1
TMO=${1:-1200}
BMC=harnesses/eval_alu/eval_alu_bmc.c
SR=$(find harnesses -name '*.c' ! -name '*_main.c' ! -name '*_bmc.c')
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

# One cell per (op x width); 0xd0 exercises the eval_max_bound fallback
# arm (BPF_OP values with no dedicated operator). 4-way batches.
OPS="add:0x00 sub:0x10 mul:0x20 div:0x30 or:0x40 and:0x50 lsh:0x60
     rsh:0x70 neg:0x80 mod:0x90 xor:0xa0 mov:0xb0 arsh:0xc0 fallback:0xd0"

echo "=== FIXED (expect all PASS) — the dispatcher glue result ==="
n=0
for entry in $OPS; do
	name=${entry%%:*}; code=${entry##*:}
	for w in 32 64; do
		cell "fixed-$name$w" -DALL_FIXES -DBMC_OP="$code" -DBMC_"$w" &
		n=$((n + 1)); [ $((n % 4)) -eq 0 ] && wait
	done
done
wait

echo
echo "=== SANITY (expect FAIL — proves the asserts are reachable) ==="
cell sanity-add32 -DALL_FIXES -DBMC_OP=0x00 -DBMC_32 -DBMC_SANITY &
cell sanity-mov64 -DALL_FIXES -DBMC_OP=0xb0 -DBMC_64 -DBMC_SANITY &
wait

echo
echo "counterexample traces (if any) are under: $OUT"
