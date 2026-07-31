#!/usr/bin/env bash

cd "$(dirname "$0")" || exit 1
TMO=${1:-120}
WIDTH=${WIDTH:-64}
SR="harnesses/eval_neg/eval_neg.c"
BMC=harnesses/eval_neg/eval_neg_tight_bmc.c
OUT=$(mktemp -d)

WFLAG=
[ "$WIDTH" = 32 ] && WFLAG=-DBMC_32

TFLAG=
[ "${TIGHTEN:-0}" = 1 ] && TFLAG=-DFIX_NEG_ZERO

SYSINC=
if [ "$(uname)" = Linux ]; then
	GCC_INC=$(gcc -print-file-name=include 2>/dev/null)
	[ -f "$GCC_INC/stddef.h" ] && SYSINC="-I$GCC_INC"
fi

verdict() {
	local f; f=$(mktemp "$OUT/cell.XXXXXX")
	esbmc "$@" $WFLAG $TFLAG $SYSINC -DALL_FIXES --timeout "${TMO}s" $BMC $SR >"$f" 2>&1
	if   grep -q "VERIFICATION FAILED"     "$f"; then echo ATTAINED
	elif grep -q "VERIFICATION SUCCESSFUL" "$f"; then echo LOOSE
	elif grep -qi "Timed out"              "$f"; then echo TIMEOUT
	else echo "ERR($f)"; fi
}

classify() {
	case "$1/$2" in
		ATTAINED/*)        echo "BOTH" ;;
		LOOSE/ATTAINED)    echo "PER-TRACK-ONLY" ;;
		LOOSE/LOOSE)       echo "NEITHER" ;;
		*)                 echo "?? isect=$1 track=$2" ;;
	esac
}

echo "=== eval_neg tightness map (${WIDTH}-bit, TIGHTEN=${TIGHTEN:-0}, --timeout ${TMO}s) ==="
echo "    regime            endpoint   isect      per-track   verdict"
echo "    ----------------  ---------  ---------  ----------  -------"
for reg in POS NEG INCL0_RESTR INCL0_PERM; do
	san=$(verdict -DBMC_REG_$reg -DBMC_UMAX -DBMC_SANITY)
	[ "$san" = ATTAINED ] || echo "    !! $reg intersection domain SANITY=$san (expected ATTAINED=reachable)"
	for ep in UMAX UMIN SMAX SMIN; do
		i=$(verdict -DBMC_REG_$reg -DBMC_$ep)
		t=$(verdict -DBMC_REG_$reg -DBMC_$ep -DBMC_TRACK)
		printf '    %-16s  %-9s  %-9s  %-10s  %s\n' \
			"$reg" "$ep" "$i" "$t" "$(classify "$i" "$t")"
	done
	echo
done

echo "counterexample / solver logs under: $OUT"
