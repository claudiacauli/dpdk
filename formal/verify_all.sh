#!/usr/bin/env bash


FAILED=0

# Parallel prover tasks: one per PHYSICAL core by default; override with
# WP_PAR=n. Logical (SMT/hyperthread) counts oversubscribe the ALUs and
# slow every prover down — bad for goals near their timeout ceiling. Only
# helps passes with many goals — a single isolated goal is still one
# single-threaded prover, whatever the machine.
phys_cores() {
	if command -v lscpu >/dev/null 2>&1; then
		# unique (core, socket) pairs among online CPUs
		lscpu -b -p=Core,Socket | grep -v '^#' | sort -u | wc -l
	else
		sysctl -n hw.physicalcpu 2>/dev/null || nproc 2>/dev/null || echo 4
	fi
}
NPAR=${WP_PAR:-$(phys_cores)}

# Status colours (suppressed when stdout is not a terminal, so logs and
# CI captures stay clean): green proved, orange timeout, red failure.
if [ -t 1 ]; then
	GRN=$'\033[32m' ORG=$'\033[38;5;208m' RED=$'\033[31m' CLR=$'\033[0m'
else
	GRN='' ORG='' RED='' CLR=''
fi

# Human wall-clock: 47s, 9m51s, 1h04m.
fmt_t() {
	local s=$1
	if [ "$s" -ge 3600 ]; then
		printf '%dh%02dm' $((s / 3600)) $((s % 3600 / 60))
	elif [ "$s" -ge 60 ]; then
		printf '%dm%02ds' $((s / 60)) $((s % 60))
	else
		printf '%ds' "$s"
	fi
}

# Run one WP pass and print exactly one status line:
#     <label> - <check> - proved [(n goals)] [wall-clock]
# On failure the offending [wp] goal lines follow, indented. frama-c
# exits 0 even when goals stay unproved, so the printed "Proved goals:
# n / n" score is what certifies a pass; 0/0 (the property filter
# matched nothing, e.g. a typo'd -wp-prop) is a failure too. A timeout
# line's wall-clock can reach ~3x -wp-timeout: each scheduled prover
# (alt-ergo, z3, cvc5) gets the full budget in turn.
wp_pass() {
	local label=$1 check=$2 out np nt t0 dt
	shift 2
	t0=$SECONDS
	out=$(frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-par "$NPAR" "$@" 2>&1)
	dt=$(fmt_t $((SECONDS - t0)))
	read -r np nt <<< "$(printf '%s\n' "$out" | awk '/Proved goals:/ {
		split($0, a, "/"); n = a[1]; sub(/.*:/, "", n)
		print n + 0, a[2] + 0 }')"
	np=${np:-0}; nt=${nt:-0}
	if [ "$nt" -gt 0 ] && [ "$np" -eq "$nt" ]; then
		if [ "$nt" -gt 1 ]; then
			echo "$label - $check - ${GRN}proved${CLR} ($nt goals) [$dt]"
		else
			echo "$label - $check - ${GRN}proved${CLR} [$dt]"
		fi
	else
		FAILED=1
		if printf '%s\n' "$out" | grep -q '\[Timeout\]'; then
			echo "$label - $check - ${ORG}timeout${CLR} ($np/$nt) [$dt]"
		else
			echo "$label - $check - ${RED}FAILED${CLR} ($np/$nt) [$dt]"
		fi
		printf '%s\n' "$out" |
			grep -E "\[wp\] \[|User Error|Error" | sed 's/^/    /'
	fi
}

# Verify one harness function: every named ensures of its contract gets
# its own isolated -wp-prop pass (batched cliff goals destabilise each
# other — same reason usound/ssound were always run isolated), then one
# remainder pass covers everything else scheduled for the function:
# RTE guards, stepping-stone asserts, assigns, call preconditions,
# termination.
verify() {
	local fct= impl= prev= f p props neg=
	for f in "$@"; do
		[ "$prev" = "-wp-fct" ] && fct=$f
		prev=$f
	done
	for f in "$@"; do
		case "$f" in */"$fct".c) impl=$f ;; esac
	done
	props=$(grep -Eo 'ensures[[:space:]]+[A-Za-z_][A-Za-z_0-9]*[[:space:]]*:' "$impl" |
		sed -E 's/ensures[[:space:]]+//; s/[[:space:]]*:$//')
	for p in $props; do
		wp_pass "$fct" "$p" "$@" -wp-prop "$p"
		neg="$neg${neg:+,}-$p"
	done
	wp_pass "$fct" "side-goals" "$@" -wp-prop="$neg"
}

# ACSL lemmas (common/specs.h) are hypotheses in every PO but are goals
# in none of the -wp-fct passes below: discharge them once, up front.
# Any single TU that includes specs.h works; use the lightest.
wp_pass "specs.h" "lemmas" -wp-timeout 20 -wp-prop @lemma \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_umax_bound \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_smax_bound \
	harnesses/eval_smax_bound/eval_smax_bound_main.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_max_bound \
	harnesses/eval_max_bound/eval_max_bound_main.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -wp-timeout 20 \
	-wp-fct eval_fill_max_bound \
	harnesses/eval_fill_max_bound/eval_fill_max_bound_main.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 \
	-wp-fct eval_sub \
	harnesses/eval_sub/eval_sub_main.c \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_lsh \
	harnesses/eval_lsh/eval_lsh_main.c \
	harnesses/eval_lsh/eval_lsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify -cpp-extra-args=-DALL_FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_rsh \
	harnesses/eval_rsh/eval_rsh_main.c \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

exit $FAILED
