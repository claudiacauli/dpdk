#!/usr/bin/env bash

# Usage: verify_all.sh [--fixes|--no-fixes] [--only <function>] [--props <list>]
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
#
# --props uopt,sopt runs ONLY those named ensures, across every harness
# that has them; harnesses with none are skipped silently. Property
# filtering also skips the side-goals, isolate, helper and lemma passes,
# so it is a fast slice, NOT a certifying run -- the stones a property
# leans on are not re-proved. Use a bare run for certification.
FIXES=
ONLY=
PROPS=
MODE=--no-fixes
while [ $# -gt 0 ]; do
	case "$1" in
	--fixes)    FIXES=-cpp-extra-args=-DALL_FIXES; MODE=--fixes ;;
	--no-fixes) FIXES=; MODE=--no-fixes ;;
	--only)     shift; ONLY=${1:?--only needs a function name} ;;
	--props)    shift; PROPS=$(printf '%s' "${1:?--props needs a list}" | tr ',' ' ') ;;
	*) echo "usage: $0 [--fixes|--no-fixes] [--only <function>] [--props <list>]" >&2
	   exit 2 ;;
	esac
	shift
done
echo "mode: $MODE${ONLY:+ (only $ONLY)}${PROPS:+ (props:$(printf ' %s' $PROPS))}"
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
# WP_TIMEOUT_PCT=n scales every -wp-timeout in the suite to n% of its
# written value (default 100 = unchanged). One knob, applied here so it
# reaches every cell including the gated optimality ones.
#
# Why a scale and not lower constants: the ceilings are calibrated to the
# REFERENCE box (MacBook, frama-c 32.0 / alt-ergo 2.6.2), where eval_mul
# ssound part 18 is red at 300s and proves inside 900. A faster or
# newer-toolchain machine can run far tighter — measured 2026-07-30 on
# the 2x EPYC 9454 server (frama-c 33.0 / alt-ergo 2.6.3, cache-free,
# -wp-par 48): eval_mul ssound proves 77/77 at EVERY ceiling from 30s to
# 900s, slowest goal 26.3s, wall-clock identical throughout. There the
# ceiling only bounds the pathological case, and bounding it matters:
# provers are tried IN TURN, each getting the full budget, so one goal
# where the first prover's search goes exponential costs 3x the ceiling
# (observed: two runs at ~970s = ~70s of work + one full 900s budget).
#
# So: WP_TIMEOUT_PCT=10 on that server caps the bad case at 3x90s instead
# of 3x900s and costs nothing on the good path. Do NOT bake it into the
# constants — the reference box needs them.
scale_timeouts() {
	local a prev= pct=${WP_TIMEOUT_PCT:-100}
	SCALED=()
	for a in "$@"; do
		if [ "$prev" = -wp-timeout ] && [ "$pct" != 100 ]; then
			a=$(( a * pct / 100 ))
			[ "$a" -lt 1 ] && a=1
		fi
		prev=$a
		SCALED+=("$a")
	done
}

wp_pass() {
	local label=$1 check=$2 out np nt t0 dt
	shift 2
	scale_timeouts "$@"
	t0=$SECONDS
	out=$(frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-par "$NPAR" "${SCALED[@]}" 2>&1)
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
	local isolate_props=${ISOLATE_PROPS-}
	local skip_props=${SKIP_PROPS-}
	SPLIT_PROPS=   # env-prefix assignments to functions persist in bash
	ISOLATE_PROPS=
	SKIP_PROPS=
	local fct= impl= prev= f p props neg= extra t0
	for f in "$@"; do
		[ "$prev" = "-wp-fct" ] && fct=$f
		prev=$f
	done
	if [ -n "$ONLY" ] && [ "$fct" != "$ONLY" ]; then
		return 0
	fi
	ONLY_MATCHED=1
	t0=$SECONDS
	for f in "$@"; do
		case "$f" in */"$fct".c) impl=$f ;; esac
	done
	props=$(grep -Eo 'ensures[[:space:]]+[A-Za-z_][A-Za-z_0-9]*[[:space:]]*:' "$impl" |
		sed -E 's/ensures[[:space:]]+//; s/[[:space:]]*:$//' | awk '!seen[$0]++')
	# awk dedup: a FIX-gated contract states the same ensures name in both
	# #ifdef branches; the raw-file grep would otherwise schedule the cell
	# twice (observed: apply_mask uopt burned two full timeouts).
	# SKIP_PROPS="uopt sopt": ensures that are compile-gated OUT of this
	# cell's build (e.g. PROVE_OPTIMALITY). The grep above reads the raw
	# file, so without this the pass would run -wp-prop on a clause the
	# preprocessor removed and report a spurious FAILED (0/0). Such props
	# are proved by their own gated cell below instead.
	if [ -n "$skip_props" ]; then
		local kept=
		for p in $props; do
			case " $skip_props " in *" $p "*) ;; *) kept="$kept $p" ;; esac
		done
		props=$kept
	fi
	if [ -n "$PROPS" ]; then
		local keep=
		for p in $props; do
			case " $PROPS " in *" $p "*) keep="$keep $p" ;; esac
		done
		props=$keep
		[ -z "$props" ] && return 0
	fi
	for p in $props; do
		extra=
		case " $split_props " in *" $p "*) extra=-wp-split ;; esac
		wp_pass "$fct" "$p" "$@" $extra -wp-prop "$p"
		neg="$neg${neg:+,}-$p"
	done
	# ISOLATE_PROPS="stone1 @requires": cliff stones (and categories)
	# that flicker inside the batched side-goals run get their own
	# isolated passes (the goal-batching instability remedy).
	[ -n "$PROPS" ] && return 0
	for p in $isolate_props; do
		wp_pass "$fct" "$p" "$@" -wp-prop "$p"
		neg="$neg${neg:+,}-$p"
	done
	wp_pass "$fct" "side-goals" "$@" -wp-prop="$neg"
	echo "$fct - ${GRN}TOTAL${CLR} - [$(fmt_t $((SECONDS - t0)))]"
}

# Helper contracts: the contract-annotated static helpers (mul_sext,
# dm_sext, fi_sext, ...) are ASSUMED at their call sites by every
# -wp-fct <harness> pass but are goals in none of them — prove each in its
# own pass. FIX-gated helpers only exist in the fixed build, so the
# per-block helper lists vary with $FIXES. Respects --only.
helpers() { # <harness> <wp args...>
	local fct=$1; shift
	[ -n "$PROPS" ] && return 0
	[ -n "$ONLY" ] && [ "$fct" != "$ONLY" ] && return 0
	wp_pass "$fct" "helpers" "$@"
}

# want <fct> <prop>...: gate for cells outside verify()'s discovery
# (the PROVE_OPTIMALITY cells). True when --only/--props do not exclude
# them: --only must match the harness, and if --props filters, at least
# one of the cell's props must be requested.
want() {
	local fct=$1 p; shift
	[ -n "$ONLY" ] && [ "$fct" != "$ONLY" ] && return 1
	[ -z "$PROPS" ] && return 0
	for p; do case " $PROPS " in *" $p "*) return 0 ;; esac; done
	return 1
}

# ACSL lemmas (common/axioms.h) are hypotheses in every PO but are goals
# in none of the -wp-fct passes below: discharge them once, up front.
# Any single TU that includes specs.h works; use the lightest.
[ -n "$PROPS" ] || wp_pass "specs.h" "lemmas" -wp-timeout 20 -wp-prop @lemma \
	harnesses/eval_umax_bound/eval_umax_bound.c

# common/axioms_shift_opt.h (len2mask_shift_s), common/lemmas_canon.h
# (to_signed_canon_rt) and harnesses/eval_lsh/lemmas_canon_lsh.h
# (to_signed_canon_shift_rt, the lsh-shaped round-trip) are TU-scoped,
# so their lemmas are out of scope of the pass above. eval_rsh pulls in
# the first, eval_arsh the second, eval_lsh the third; compiling all
# three together puts every one of them in scope of a single pass. A
# lemma PO depends only on the logic definitions, so proving each once
# here covers every including TU. The axioms carry no goals here — only
# the lemmas do.
[ -n "$PROPS" ] || wp_pass "shift-opt" "lemmas" -wp-timeout 60 -wp-prop @lemma \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_lsh/eval_lsh.c

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
# Per-property split, NOT blanket: under the intersection soundness form
# usound must stay MONOLITHIC (it proves in one search; split, part01
# never closes even at 600s uncontended), while ssound and the side-goals
# batch still need splitting — the unsplit side-goals flip the uand_max
# requires-instances past the timeout.
# uopt/sopt + their witness stones are compile-gated (PROVE_OPTIMALITY)
# out of this soundness build: the stones' ground land nodes on the
# u-endpoints seed the land-axiom family inside the usound/ssound
# searches (diagnosed 2026-07-20). Their own cell follows.
SKIP_PROPS="uopt sopt" \
SPLIT_PROPS="ssound" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_and \
	harnesses/eval_and/eval_and_main.c \
	harnesses/eval_and/eval_and.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_and optimality cell: the gated build. One pass proves uopt/sopt
# and every witness stone (a stone assumes only the ones before it, so
# listing them all keeps every assumed fact a proved one). Fixed
# semantics only — the optimality clauses were derived under ALL_FIXES.
[ -n "$FIXES" ] && want eval_and uopt sopt &&
wp_pass "eval_and" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 600 \
	-wp-fct eval_and \
	-wp-prop="uopt,sopt,uopt_idem_max,uopt_idem_min,sopt_half_max,sopt_half_min,sopt_rt_max,sopt_rt_min,sopt_idem_max,sopt_idem_min" \
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
# 900s not 60: a lemma is proved ONCE, so a generous ceiling costs nothing
# and keeps a slow goal from flickering red (a red lemma would silently
# prop up ssound). The two signed FOLDED statements (mul_ssound_overflow /
# mul_ssound_const) are no longer goals here: red at 900s batched AND
# 1800s isolated under the intersection-form bin_witness (2026-07-28),
# they are now validated AXIOMS — tier notes in eval_mul.h, enumeration
# in axiom_validation/brute_mul_lemmas.c, ESBMC cells (server tier) in
# validate_specs_axioms.c. The remaining lemmas prove in seconds.
# TU-scoped (unlike specs.h's global lemmas): eval_mul.c is the only TU that
# includes axioms_mul.h, so a --only run of any other function need not prove
# these — skip them unless the whole suite or eval_mul itself is being run.
# (if/fi, not `A && B || C`: the &&/|| chain parses as `(A && B) || C`,
# which ran this 15-minute pass in EVERY --only block — and its red
# lemma poisoned the exit code of otherwise all-green runs, 2026-07-20.)
if { [ -z "$ONLY" ] || [ "$ONLY" = eval_mul ]; } && [ -z "$PROPS" ]; then
# -DPROVE_MUL_LEMMAS: mul_sext_congr is in scope ONLY here — it exists
# to prove mul_ssound_const and it perturbs swidth/optimality when left
# in the soundness TU (see axioms_mul.h).
wp_pass "axioms_mul.h" "lemmas" -wp-timeout 900 -wp-prop @lemma \
	-cpp-extra-args=-DPROVE_MUL_LEMMAS \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c
fi

# The folded statements (eval_mul.h: mul_usound_* proved lemmas,
# mul_ssound_* validated axioms) state each branch's soundness against the
# folded predicate, so every soundness goal closes by ONE instantiation
# instead of a per-goal e-matching search. Without them the hardest
# overflow x fallback part did not close even at 1800s.
# 900s not 300 (2026-07-28): the usound_link_*/ssound_link_* relay stones
# (eval_mul.c multiply branches) closed the last red pair (part 13 of each
# track) but their product e-nodes sit in every multiply-path part, and
# ssound part 18 — margin-zero per rule "contract growth tips cliff goals"
# — moved past 300s: red at 300, proves inside 900 on the reference box.
# A generous ceiling costs nothing when the goals prove.
# uopt/sopt + their ~10 witness stones are compile-gated
# (PROVE_OPTIMALITY) out of this soundness build: the stones' nonlinear
# product e-nodes are assumed into every usound/ssound split part and
# push the tail past the ceiling (the §6l hazard, diagnosed 2026-07-20).
# Their own cell follows the helpers.
# swidth in SPLIT_PROPS (2026-07-20): it is a CLIFF goal at margin zero
# — monolithic it proved in ~1m until the day's additions (each
# individually innocent by bisection) tipped it to a 900s spin; split
# per opsz it proves 77/77 fast regardless of context.
SKIP_PROPS="uopt sopt" \
SPLIT_PROPS="usound ssound swidth" \
verify $FIXES -wp-timeout 900 \
	-wp-fct eval_mul \
	harnesses/eval_mul/eval_mul_main.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

if [ -n "$FIXES" ]; then MULH=mul_umask,mul_sext,mul_sext2; else MULH=mul_umask; fi
helpers eval_mul $FIXES -wp-timeout 60 -wp-fct $MULH \
	harnesses/eval_mul/eval_mul_main.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_mul optimality cell: the gated build (see the soundness cell's
# note). 900s not 300: uopt is a monolithic nonlinear search that spun
# past 300s on this machine while its twin sopt closes in ~80s — the
# controlled 77/77 figure used a higher ceiling, and a generous one
# costs nothing when the goals prove.
[ -n "$FIXES" ] && want eval_mul uopt sopt &&
wp_pass "eval_mul" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 900 \
	-wp-fct eval_mul \
	-wp-prop="uopt,sopt,uopt_wit_umax,uopt_wit_umin,uopt_sum_umax,uopt_sum_umin,sopt_wit_smax,sopt_wit_smin,sopt_pat_id,sopt_sum_smax32,sopt_sum_smax64,sopt_sum_smin" \
	harnesses/eval_mul/eval_mul_main.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_divmod: unsigned div/mod ranges + the sign-contiguity signed
# reinterpretation. The DivModBounds axioms (harness-scoped axioms_div.h;
# NIA- and ESBMC-validated, no Qed lemmas so no extra @lemma pass) give the
# linear div/mod facts, after which every goal — usound/ssound included —
# proves monolithic in under a minute; no split, no stones.
verify $FIXES -wp-timeout 300 \
	-wp-fct eval_divmod \
	harnesses/eval_divmod/eval_divmod_main.c \
	harnesses/eval_divmod/eval_divmod.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

[ -n "$FIXES" ] && helpers eval_divmod $FIXES -wp-timeout 60 \
	-wp-fct dm_sext \
	harnesses/eval_divmod/eval_divmod_main.c \
	harnesses/eval_divmod/eval_divmod.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_neg: pattern negation with cross-track limit exchange. The spec's
# neg_pat is LINEAR (x==0 ? 0 : msk+1-x), so no operator axioms are needed
# at all — the shared land/wrap set plus the neg_sext helper contract carry
# almost every goal monolithic in seconds. 1200s not 300: ssound is the
# one slow search (~15m wall on this machine, proves 1/1 isolated at
# 1200s, 2026-07-20 — it is a ceiling case, not a missing lemma; a
# TU-wide canon lemma tried instead REGRESSED usound, see eval_neg.c).
verify $FIXES -wp-timeout 1200 \
	-wp-fct eval_neg \
	harnesses/eval_neg/eval_neg_main.c \
	harnesses/eval_neg/eval_neg.c

[ -n "$FIXES" ] && helpers eval_neg $FIXES -wp-timeout 60 \
	-wp-fct neg_sext \
	harnesses/eval_neg/eval_neg_main.c \
	harnesses/eval_neg/eval_neg.c

# eval_defined: the operand-definedness rejection (upstream helper shared
# by the ALU/jump/store/call evaluators) — exact iff contract, proves in
# seconds. No FIX gate.
verify -wp-timeout 20 \
	-wp-fct eval_defined \
	harnesses/eval_defined/eval_defined_main.c \
	harnesses/eval_defined/eval_defined.c

# eval_fill_imm64: the exact-constant primitive (unsigned track = the
# w-bit pattern, signed track = its canonical reading).
# FIX_FILL_IMM_SIGNED_32 (32-bit negative pattern stored unextended in
# the signed track) is the gated bug; the fi_sext helper only exists in
# the fixed build.
verify $FIXES -wp-timeout 60 \
	-wp-fct eval_fill_imm64 \
	harnesses/eval_fill_imm64/eval_fill_imm64_main.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

[ -n "$FIXES" ] && helpers eval_fill_imm64 $FIXES -wp-timeout 60 \
	-wp-fct fi_sext \
	harnesses/eval_fill_imm64/eval_fill_imm64_main.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

# eval_fill_imm: constant materialisation over eval_fill_imm64's
# contract — all goals prove in seconds.
verify $FIXES -wp-timeout 60 \
	-wp-fct eval_fill_imm \
	harnesses/eval_fill_imm/eval_fill_imm_main.c \
	harnesses/eval_fill_imm/eval_fill_imm.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

# uopt/sopt compile-gated out (PROVE_OPTIMALITY): the unconditional uopt's
# bare existential tipped eval_alu cliff stones when assumed at call sites
# (2026-07-21). Their own cell follows.
SKIP_PROPS="uopt sopt" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_apply_mask optimality cell: the gated build (fixed semantics only —
# the unconditional u-clause was derived under FIX_APPLY_MASK_OPT). The
# straddle/keep witness stones are FIX-gated, not PROVE-gated, so the main
# pass above still proves them; here they are assumed-and-proved context.
[ -n "$FIXES" ] && want eval_apply_mask uopt sopt &&
wp_pass "eval_apply_mask" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	-wp-prop="uopt,sopt" \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

# eval_sub: NOT split — measured on the certified run of 2026-07-10:
# split, its ssound takes 30'49" across 378 parts and unchanged_v
# 11'48"; monolithic the same goals prove in 14s and ~1s.
# The signed uniform-wrap stones (FIX_SUB_SIGNED_OVFL_OPT) flicker in the
# batched side-goals cell (2026-07-21: the two _min twins timed out while
# the _max twins proved); isolate all four.
# ${FIXES:+...}: these four asserts live inside #ifdef
# FIX_{ADD,SUB}_SIGNED_OVFL_OPT, which fixes.h defines only under
# ALL_FIXES. Naming them unconditionally made every --no-fixes run
# print four FAILED (0/0) lines per operator -- zero goals matched,
# indistinguishable in the transcript from a real upstream-defect
# red, in exactly the mode whose reds ARE the bug report
# (2026-07-28 audit; the same hazard is documented for eval_alu
# further down).
ISOLATE_PROPS="${FIXES:+sopt_ofwrap_min sopt_ofwrap_max sopt_ufwrap_min sopt_ufwrap_max}" \
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
# ${FIXES:+...}: these four asserts live inside #ifdef
# FIX_{ADD,SUB}_SIGNED_OVFL_OPT, which fixes.h defines only under
# ALL_FIXES. Naming them unconditionally made every --no-fixes run
# print four FAILED (0/0) lines per operator -- zero goals matched,
# indistinguishable in the transcript from a real upstream-defect
# red, in exactly the mode whose reds ARE the bug report
# (2026-07-28 audit; the same hazard is documented for eval_alu
# further down).
ISOLATE_PROPS="${FIXES:+sopt_ofwrap_min sopt_ofwrap_max sopt_ufwrap_min sopt_ufwrap_max}" \
verify $FIXES -wp-timeout 3000 \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

# 1800s not 600 (2026-07-20): usound parts 10/11 and ssound parts 06/11
# are red-SLOW true goals that resisted both a shaped lemma
# (to_signed_canon_shift_rt, proved and in scope) and bridge stones —
# the same goal family for which eval_arsh needed exactly this ceiling.
verify $FIXES -wp-timeout 1800 -wp-split \
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

# The dispatcher's lemma base, proved STANDALONE and FIRST. eval_alu.c
# includes both headers, and -wp-fct never schedules lemma goals, so the
# eval_alu cell below ASSUMES all 76 of these without proving any. An
# unproved lemma there would silently manufacture the composition proof
# (it has happened twice: docs/review_04_composition.md §5). These two
# cells are what make the cell below mean something.
# Neither header contains an axiom: the composition adds no trusted base.
# Gated like axioms_mul.h below: only eval_alu.c includes these headers, so
# a --only run of anything else need not prove them, and a --props run
# cannot match a @lemma goal at all. Without the gate they cost ~2 minutes
# on EVERY --only block — the exact waste that comment records.
# if/fi, not `A && B || C`: that chain parses as `(A && B) || C`.
if { [ -z "$ONLY" ] || [ "$ONLY" = eval_alu ]; } && [ -z "$PROPS" ]; then
wp_pass "axioms_alu.h" "lemmas" -wp-timeout 600 -wp-prop @lemma \
	harnesses/eval_alu/axioms_alu_check.c

wp_pass "lemmas_deliver.h" "lemmas" -wp-timeout 600 -wp-prop @lemma \
	harnesses/eval_alu/lemmas_deliver_check.c
fi

# eval_alu: the dispatcher glue theorem (error semantics, register
# invariant re-established at the op width; framing is certified by the
# assigns clause — an explicit quantified frame ensures explodes, don't
# add one; monolithic only — split makes uwidth/swidth flicker). Its TU
# composes every operator implementation, so all scoped axiom families
# are in scope of every PO; the vld_*/wid_*/ord_d stones hand the
# operator requires-instances their facts directly.
# 1200s: the two heaviest side-goal stones (sx_vld64 ~578s uncontended,
# and the sign-extension stones over the branch-merged rs heap) need the
# headroom, like eval_arsh's usound.
# (vld_s32/vld_s64/vld_d were removed here 2026-07-19: those range_validity
# stones were FALSE and are DELETED from eval_alu.c; source ordering now
# comes from ord_s2/ord_d2. Leaving the name in this isolate list makes the
# pass match 0 goals and report a spurious FAILED (0/0).)
# -no-warn-unaligned-pointer: the evst double indirection makes the
# kernel emit an \aligned alarm, but WP does not implement \aligned at
# all ("not yet implemented" — hypotheses dropped, goal degenerates), so
# the alarm is unprovable noise in a WP pipeline; alignment holds for any
# real allocation and is cross-checked by the BMC memsafety dimension.
# sx_vld*/ord_d* split per register / per track 2026-07-28: the joined
# stones went margin-zero as the operator contracts grew (three isolated
# 1200s runs: sx_vld32 + ord_dk deterministically red, ord_dx at ~half
# ceiling), with every single candidate culprit exonerated — the cliff
# pattern; half-conclusions restored the margin.
# This cell also carries the composition theorem (usound/ssound) and its
# 15 delivery + 22 per-arm + 2 merge stones, merged 2026-07-30. The
# source list below must stay complete: with an operator .c missing,
# Frama-C warns `missing-spec`, gives that operator a default contract,
# and the per-arm stone for it proves nothing — green and meaningless.
ISOLATE_PROPS="sx_vld32_rs sx_vld32_rd sx_vld64_rs sx_vld64_rd ord_dx_u ord_dx_s ord_dk_u ord_dk_s @requires" \
verify $FIXES -wp-timeout 1200 -no-warn-unaligned-pointer \
	-wp-fct eval_alu \
	harnesses/eval_alu/eval_alu_main.c \
	harnesses/eval_alu/eval_alu.c \
	harnesses/eval_defined/eval_defined.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_fill_imm/eval_fill_imm.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_lsh/eval_lsh.c \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_and/eval_and.c \
	harnesses/eval_or/eval_or.c \
	harnesses/eval_xor/eval_xor.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_divmod/eval_divmod.c \
	harnesses/eval_neg/eval_neg.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_umax_bits/eval_umax_bits.c

# 1200s: the slowest usound split part flickers at the 600s line under
# load; uncontended it proves with margin at 1200.
verify $FIXES -wp-timeout 1800 -wp-split \
	-wp-fct eval_arsh \
	harnesses/eval_arsh/eval_arsh_main.c \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c

# EXECUTOR AGREEMENT (exec_* family): the interpreter case-arms in
# lib/bpf/bpf_exec.c compute exactly the SEM_* concrete semantics
# (common/semantics.h) the validator predicates abstract — the left
# arrow of the assurance chain (see harnesses/exec_alu/exec_alu.c).
# -no-warn-unaligned-pointer: that kernel option makes RTE emit
# \aligned alarms for the scalar register-array indexing, which WP
# cannot translate ("\aligned not yet implemented") and which
# degenerate EVERY goal in the TU; alignment is real in the caller
# (the register file is a uint64_t stack array). No $FIXES: the
# harness bodies are verbatim upstream case-arms, no gates.
if { [ -z "$ONLY" ] || [ "$ONLY" = exec_alu ]; } && [ -z "$PROPS" ]; then
ONLY_MATCHED=1
wp_pass "exec_alu" "agreement" -no-warn-unaligned-pointer -wp-timeout 120 \
	harnesses/exec_alu/exec_alu.c
fi

if [ -n "$ONLY" ] && [ -z "$ONLY_MATCHED" ]; then
	echo "error: --only $ONLY matched no verify block" >&2
	FAILED=1
fi
exit $FAILED
