#!/usr/bin/env bash

# Usage: verify_all.sh [--fixes|--no-fixes] [--only <function>]
#
# --no-fixes (the DEFAULT) verifies the faithful port of the upstream
# code: the goals covered by FIX_* gates are then EXPECTED to fail —
# that failure list is the bug report. --fixes (-DALL_FIXES) verifies
# the fixed semantics and is the configuration expected to be fully
# green; use it for certified runs.
#
# --only eval_lsh runs just that harness's block (the lemma pass still
# runs: lemmas are assumed everywhere, so they must be proved even in a
# single-method run).
FIXES=
ONLY=
MODE=--no-fixes
while [ $# -gt 0 ]; do
	case "$1" in
	--fixes)    FIXES=-cpp-extra-args=-DALL_FIXES; MODE=--fixes ;;
	--no-fixes) FIXES=; MODE=--no-fixes ;;
	--only)     shift; ONLY=${1:?--only needs a function name} ;;
	*) echo "usage: $0 [--fixes|--no-fixes] [--only <function>]" >&2
	   exit 2 ;;
	esac
	shift
done
echo "mode: $MODE${ONLY:+ (only $ONLY)}"
ONLY_MATCHED=

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
#
# Split control: put -wp-split in the block args to split EVERY pass, or
# prefix the call with SPLIT_PROPS="p1 p2" to split only those
# properties (eval_add needs usound split but ssound monolithic — the
# two goals sit on opposite sides of the split trade-off).
verify() {
	local split_props=${SPLIT_PROPS-}
	SPLIT_PROPS=   # env-prefix assignments to functions persist in bash
	local fct= impl= prev= f p props neg= extra
	for f in "$@"; do
		[ "$prev" = "-wp-fct" ] && fct=$f
		prev=$f
	done
	if [ -n "$ONLY" ] && [ "$fct" != "$ONLY" ]; then
		return 0
	fi
	ONLY_MATCHED=1
	for f in "$@"; do
		case "$f" in */"$fct".c) impl=$f ;; esac
	done
	props=$(grep -Eo 'ensures[[:space:]]+[A-Za-z_][A-Za-z_0-9]*[[:space:]]*:' "$impl" |
		sed -E 's/ensures[[:space:]]+//; s/[[:space:]]*:$//')
	for p in $props; do
		extra=
		case " $split_props " in *" $p "*) extra=-wp-split ;; esac
		wp_pass "$fct" "$p" "$@" $extra -wp-prop "$p"
		neg="$neg${neg:+,}-$p"
	done
	wp_pass "$fct" "side-goals" "$@" -wp-prop="$neg"
}

# ACSL lemmas (common/axioms.h) are hypotheses in every PO but are goals
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

verify $FIXES -wp-timeout 60 \
	-wp-fct eval_umax_bits \
	harnesses/eval_umax_bits/eval_umax_bits_main.c \
	harnesses/eval_umax_bits/eval_umax_bits.c

verify $FIXES -wp-timeout 60 \
	-wp-fct eval_uand_max \
	harnesses/eval_uand_max/eval_uand_max_main.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_umax_bits/eval_umax_bits.c

verify $FIXES -wp-timeout 60 \
	-wp-fct eval_uor_max \
	harnesses/eval_uor_max/eval_uor_max_main.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_umax_bits/eval_umax_bits.c

# Deliberately WITHOUT eval_umax_bits.c: eval_and only needs the
# contracts of its DIRECT callees (eval_uand_max, eval_smax_bound), and
# umax_bits' .c would drag the ClzWindow axioms into every PO here.
# -wp-split: the unsplit side-goals batch flips the uand_max
# requires-instances past the timeout; split, all parts prove fast.
verify $FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_and \
	harnesses/eval_and/eval_and_main.c \
	harnesses/eval_and/eval_and.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_or mirrors eval_and (direct callees eval_uor_max + eval_smax_bound;
# umax_bits.c left out for the same ClzWindow reason). Only ssound needs
# the opsz case split (its signed-OR round-trip resolves per concrete
# mask); the bound goals prove faster monolithic.
SPLIT_PROPS=ssound \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_or \
	harnesses/eval_or/eval_or_main.c \
	harnesses/eval_or/eval_or.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_xor over-approximates the XOR by the OR estimate eval_uor_max
# (a^b <= a|b), so it mirrors eval_or's TU (faithful port, no FIX gate).
# BOTH soundness goals need the opsz case split — usound chains
# lxor_le_lor through uor_cover, whose width bound only resolves per
# concrete mask; the structural/bounds goals prove monolithic.
SPLIT_PROPS="usound ssound" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_xor \
	harnesses/eval_xor/eval_xor_main.c \
	harnesses/eval_xor/eval_xor.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_mul: nonlinear multiply, the hardest operator. Both soundness goals
# need the opsz/mask split — usound's mask-strip and ssound's signed
# round-trip / uint-wrap bridge resolve per concrete mask. axioms_mul.h
# (the half_mask_* Qed lemmas plus the mul monotonicity / bound / wrap
# axioms) is included ONLY by eval_mul.c, so its lemmas need their own
# @lemma pass here: the top-level pass runs over a TU that never sees them.
# 450s not 60: mul_ssound_overflow (the to_signed-strip + framing lemma) is a
# slow nonlinear goal — ~76s on the reference box, more on a slower one — and a
# lemma is proved ONCE, so a generous ceiling costs nothing and keeps it from
# flickering red (a red lemma would silently prop up ssound). The other 16
# lemmas prove in seconds.
wp_pass "axioms_mul.h" "lemmas" -wp-timeout 450 -wp-prop @lemma \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# The mul_usound_overflow / mul_ssound_overflow lemmas (eval_mul.h) state
# each overflow branch's soundness against the folded predicate, so every
# soundness goal closes by ONE lemma instantiation instead of a per-goal
# e-matching search — 300s is ample (whole-property wall ~4m, no single part
# over ~2m). Without those lemmas the hardest overflow x fallback part did
# not close even at 1800s.
SPLIT_PROPS="usound ssound" \
verify $FIXES -wp-timeout 300 \
	-wp-fct eval_mul \
	harnesses/eval_mul/eval_mul_main.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

verify $FIXES -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_sub: NOT split — measured on the certified run of 2026-07-10:
# split, its ssound takes 30'49" across 378 parts and unchanged_v
# 11'48"; monolithic the same goals prove in 14s and ~1s.
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_sub \
	harnesses/eval_sub/eval_sub_main.c \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

# eval_add: ssound deliberately NOT split — its quantified wrap-core
# lives whole in every split leaf (11 of 1134 parts time out at 600s on
# both machines) while the monolith proves in one Z3 search (2'20"
# MacBook / 1'42" server, with the arsh axioms scoped out of this TU —
# see common/axioms_arsh.h). usound is the opposite: its monolith
# flickers past 3000s while the 1134 split parts prove in minutes.
SPLIT_PROPS=usound \
verify $FIXES -wp-timeout 3000 \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify $FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_lsh \
	harnesses/eval_lsh/eval_lsh_main.c \
	harnesses/eval_lsh/eval_lsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

verify $FIXES -wp-timeout 600 -wp-split \
	-wp-fct eval_rsh \
	harnesses/eval_rsh/eval_rsh_main.c \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

# 1200s: the slowest usound split part flickers at the 600s line under
# load; uncontended it proves with margin at 1200.
verify $FIXES -wp-timeout 1800 -wp-split \
	-wp-fct eval_arsh \
	harnesses/eval_arsh/eval_arsh_main.c \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c

if [ -n "$ONLY" ] && [ -z "$ONLY_MATCHED" ]; then
	echo "error: --only $ONLY matched no verify block" >&2
	FAILED=1
fi
exit $FAILED
