#!/usr/bin/env bash

export FRAMAC_WP_CACHE=none

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

phys_cores() {
	if command -v lscpu >/dev/null 2>&1; then
		lscpu -b -p=Core,Socket | grep -v '^#' | sort -u | wc -l
	else
		sysctl -n hw.physicalcpu 2>/dev/null || nproc 2>/dev/null || echo 4
	fi
}
NPAR=${WP_PAR:-$(phys_cores)}

if [ -t 1 ]; then
	GRN=$'\033[32m' ORG=$'\033[38;5;208m' RED=$'\033[31m' CLR=$'\033[0m'
else
	GRN='' ORG='' RED='' CLR=''
fi

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
	out=$(frama-c -rte -wp -wp-cache=none -wp-prover alt-ergo,z3,cvc5 -wp-par "$NPAR" "${SCALED[@]}" 2>&1)
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

verify() {
	local split_props=${SPLIT_PROPS-}
	local isolate_props=${ISOLATE_PROPS-}
	local skip_props=${SKIP_PROPS-}
	SPLIT_PROPS=
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
	[ -n "$PROPS" ] && return 0
	for p in $isolate_props; do
		wp_pass "$fct" "$p" "$@" -wp-prop "$p"
		neg="$neg${neg:+,}-$p"
	done
	wp_pass "$fct" "side-goals" "$@" -wp-prop="$neg"
	echo "$fct - ${GRN}TOTAL${CLR} - [$(fmt_t $((SECONDS - t0)))]"
}

helpers() {
	local fct=$1; shift
	[ -n "$PROPS" ] && return 0
	[ -n "$ONLY" ] && [ "$fct" != "$ONLY" ] && return 0
	wp_pass "$fct" "helpers" "$@"
}

want() {
	local fct=$1 p; shift
	[ -n "$ONLY" ] && [ "$fct" != "$ONLY" ] && return 1
	[ -z "$PROPS" ] && return 0
	for p; do case " $PROPS " in *" $p "*) return 0 ;; esac; done
	return 1
}

[ -n "$PROPS" ] || wp_pass "specs.h" "lemmas" -wp-timeout 20 -wp-prop @lemma \
	harnesses/eval_umax_bound/eval_umax_bound.c

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

SKIP_PROPS="uopt sopt" \
SPLIT_PROPS="ssound" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_and \
	harnesses/eval_and/eval_and_main.c \
	harnesses/eval_and/eval_and.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

[ -n "$FIXES" ] && want eval_and uopt sopt &&
wp_pass "eval_and" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 600 \
	-wp-fct eval_and \
	-wp-prop="uopt,sopt,uopt_idem_max,uopt_idem_min,sopt_half_max,sopt_half_min,sopt_rt_max,sopt_rt_min,sopt_idem_max,sopt_idem_min" \
	harnesses/eval_and/eval_and_main.c \
	harnesses/eval_and/eval_and.c \
	harnesses/eval_uand_max/eval_uand_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

SPLIT_PROPS=ssound \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_or \
	harnesses/eval_or/eval_or_main.c \
	harnesses/eval_or/eval_or.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

SPLIT_PROPS="usound ssound" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_xor \
	harnesses/eval_xor/eval_xor_main.c \
	harnesses/eval_xor/eval_xor.c \
	harnesses/eval_uor_max/eval_uor_max.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

if { [ -z "$ONLY" ] || [ "$ONLY" = eval_mul ]; } && [ -z "$PROPS" ]; then
wp_pass "axioms_mul.h" "lemmas" -wp-timeout 900 -wp-prop @lemma \
	-cpp-extra-args=-DPROVE_MUL_LEMMAS \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c
fi

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

[ -n "$FIXES" ] && want eval_mul uopt sopt &&
wp_pass "eval_mul" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 900 \
	-wp-fct eval_mul \
	-wp-prop="uopt,sopt,uopt_wit_umax,uopt_wit_umin,uopt_sum_umax,uopt_sum_umin,sopt_wit_smax,sopt_wit_smin,sopt_pat_id,sopt_sum_smax32,sopt_sum_smax64,sopt_sum_smin" \
	harnesses/eval_mul/eval_mul_main.c \
	harnesses/eval_mul/eval_mul.c \
	harnesses/eval_umax_bound/eval_umax_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

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

verify $FIXES -wp-timeout 1200 \
	-wp-fct eval_neg \
	harnesses/eval_neg/eval_neg_main.c \
	harnesses/eval_neg/eval_neg.c

[ -n "$FIXES" ] && helpers eval_neg $FIXES -wp-timeout 60 \
	-wp-fct neg_sext \
	harnesses/eval_neg/eval_neg_main.c \
	harnesses/eval_neg/eval_neg.c

verify -wp-timeout 20 \
	-wp-fct eval_defined \
	harnesses/eval_defined/eval_defined_main.c \
	harnesses/eval_defined/eval_defined.c

verify $FIXES -wp-timeout 60 \
	-wp-fct eval_fill_imm64 \
	harnesses/eval_fill_imm64/eval_fill_imm64_main.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

[ -n "$FIXES" ] && helpers eval_fill_imm64 $FIXES -wp-timeout 60 \
	-wp-fct fi_sext \
	harnesses/eval_fill_imm64/eval_fill_imm64_main.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

verify $FIXES -wp-timeout 60 \
	-wp-fct eval_fill_imm \
	harnesses/eval_fill_imm/eval_fill_imm_main.c \
	harnesses/eval_fill_imm/eval_fill_imm.c \
	harnesses/eval_fill_imm64/eval_fill_imm64.c

SKIP_PROPS="uopt sopt" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

[ -n "$FIXES" ] && want eval_apply_mask uopt sopt &&
wp_pass "eval_apply_mask" "optimality" \
	"-cpp-extra-args=-DALL_FIXES -DPROVE_OPTIMALITY" -wp-timeout 600 \
	-wp-fct eval_apply_mask \
	-wp-prop="uopt,sopt" \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

ISOLATE_PROPS="${FIXES:+sopt_ofwrap_min sopt_ofwrap_max sopt_ufwrap_min sopt_ufwrap_max}" \
verify $FIXES -wp-timeout 600 \
	-wp-fct eval_sub \
	harnesses/eval_sub/eval_sub_main.c \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

SPLIT_PROPS=usound \
ISOLATE_PROPS="${FIXES:+sopt_ofwrap_min sopt_ofwrap_max sopt_ufwrap_min sopt_ufwrap_max}" \
verify $FIXES -wp-timeout 3000 \
	-wp-fct eval_add \
	harnesses/eval_add/eval_add_main.c \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

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

if { [ -z "$ONLY" ] || [ "$ONLY" = eval_alu ]; } && [ -z "$PROPS" ]; then
wp_pass "axioms_alu.h" "lemmas" -wp-timeout 600 -wp-prop @lemma \
	harnesses/eval_alu/axioms_alu_check.c

wp_pass "lemmas_deliver.h" "lemmas" -wp-timeout 600 -wp-prop @lemma \
	harnesses/eval_alu/lemmas_deliver_check.c
fi

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

verify $FIXES -wp-timeout 1800 -wp-split \
	-wp-fct eval_arsh \
	harnesses/eval_arsh/eval_arsh_main.c \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c

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
