#!/usr/bin/env python3
"""
report.py — build the verification report tables for the formal/ harnesses.

Emits two Markdown tables, one row per method (a method is any m with
harnesses/<m>/<m>_bmc.c next to its implementation <m>.c):

  1. Contract table — one column per ACSL `ensures <name>:` found in the
     method's contract; each cell holds three sub-verdicts in the fixed
     order  CBMC · ESBMC · WP.
  2. Memsafety table — one column per check category below; same three
     sub-verdicts per cell.

Glyphs:  Y proved   X violated (counterexample)   T timeout/unknown
         ! fails by design (documented intentional behaviour)
         E tool/config error (parse failure, no goal, tool missing)
         - not applicable / no such check / property not stated

'E' is deliberately distinct from 'T' and '-': a report whose reds ARE
the deliverable must never let "the tool broke" hide inside "unknown" or
"not applicable" (review_03 finding A7).

Check-category mapping (best effort; '-' where a tool has no equivalent):

  category           CBMC flag                   ESBMC flag                  WP (-rte goal)
  bounds             --bounds-check              (default run)               mem_access
  pointer            --pointer-check             (default run)               mem_access
  division           --div-by-zero-check         (default run)               division_by_zero
  signed-overflow    --signed-overflow-check     --overflow-check            signed_overflow
  unsigned-overflow  --unsigned-overflow-check   --unsigned-overflow-check   (not generated)
  shift              --undefined-shift-check     --ub-shift-check            shift
  memory-leak        --memory-leak-check         --memory-leak-check         -
  nan                --nan-check                 --nan-check                 -
  struct-fields      -                           --struct-fields-check       -
  data-races         -                           --data-races-check          -
  deadlock           -                           --deadlock-check            -
  lock-order         -                           --lock-order-check          -
  atomicity          -                           --atomicity-check           -

Mode (positional, default 'original'):
  report.py fixed      all tools run with -DALL_FIXES: the FIX-gated
                       semantics, the configuration verify_all.sh --fixes
                       certifies green.
  report.py original   the faithful upstream port. The goals covered by
                       FIX_* gates are EXPECTED to show X/T here — the
                       delta against the 'fixed' report is the bug list.
  Output files are suffixed with the mode (…_<platform>_<mode>.{md,csv,
  jsonl,html}, latest_<mode>.*), so the two reports can sit side by side.

Notes:
  - WP's mem_access guards cover both 'bounds' and 'pointer', so those two
    WP sub-cells always agree.
  - unsigned-overflow is expected to fail: the eval_* interval arithmetic
    wraps by design (see bmc_all.sh). Reported as '!'.
  - BMC assertions are attributed to contract properties via the trailing
    /* name */ comments on the assert lines in *_bmc.c — keep them. The
    token 'ord' expands to uord+sord; multiple names may share one assert.
  - WP passes use each method's OWN translation unit (its implementation
    plus transitive callees, like verify_all.sh's per-harness file
    lists), NOT all harness sources: pulling an unrelated harness into
    the TU drags its scoped axioms (e.g. common/axioms_arsh.h) into
    every PO and can push unrelated cliff goals past their timeout.
    -wp-split choices mirror verify_all.sh (WP_SPLIT_* below); keep the
    two in sync. verify_all.sh remains the certified configuration.
  - Runs are serial on purpose: provers fight for cores otherwise. A full
    run is dominated by the WP soundness goals. With the driver's real
    ceilings mirrored (eval_add 3000s, eval_arsh/eval_lsh 1800s,
    eval_neg 1200s, eval_alu 1200s) a full two-table run is an
    OVERNIGHT job, not 10-30 minutes — budget hours, or use --skip-bmc /
    --methods for a partial pass.
  - Re-rendering is decoupled from verifying: `--render-from <jsonl>`
    rebuilds the md/csv/html from a previous run's jsonl in under a
    second, so presentation work never costs a re-verification.
  - `--delta old.jsonl new.jsonl` writes the fixed-vs-original delta
    table: the cells that change verdict between the two modes ARE the
    upstream bug list.

Beyond the three engines, the certified driver (verify_all.sh) also runs
passes that carry every WP result but produce no per-property cell:
ACSL @lemma passes, helper-contract cells, per-function side-goal
passes, the executor-agreement family, ESBMC axiom-validation cells and
the \\false consistency probes. Those are summarised in the HTML's
"Supporting passes" section (driver-certified, not re-run here) so a
reader cannot mistake a green matrix for the whole proof.
"""

import argparse
import csv
import datetime
import glob
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import time

OK, FAIL, TIMEOUT, NA, EXPECTED, ERROR = "Y", "X", "T", "-", "!", "E"

WP_PROVERS = "alt-ergo,z3,cvc5"

# Set in main() from the positional mode argument ('fixed' | 'original').
MODE = "original"
DEFS = []

# WP parallelism. The driver uses physical cores (verify_all.sh:45-53);
# frama-c's default is 4, which under-uses the machine on a run whose
# ceilings are now measured in tens of minutes.
NPAR = os.cpu_count() or 4

# Split-vs-monolith is a per-goal empirical choice measured in
# verify_all.sh (see its block comments); this mirrors the driver —
# keep the two in sync.
#
# eval_and is NOT here (2026-07-29 audit): the driver splits only its
# ssound (SPLIT_PROPS="ssound", verify_all.sh:283) and requires usound
# MONOLITHIC — "split, part01 never closes even at 600s uncontended"
# (verify_all.sh:273-277). A blanket entry here silently forced the
# split on every eval_and prop.
WP_SPLIT_METHODS = {"eval_lsh", "eval_rsh", "eval_arsh"}
WP_SPLIT_PROPS = {"eval_add": {"usound"}, "eval_or": {"ssound"},
                  "eval_xor": {"usound", "ssound"},
                  "eval_and": {"ssound"},
                  # swidth: a cliff goal, monolithic it spins at 900s,
                  # split per opsz it proves 77/77 (verify_all.sh:377-382)
                  "eval_mul": {"usound", "ssound", "swidth"}}

# Extra frama-c flags the driver passes for specific functions. eval_alu:
# the evst double indirection makes RTE emit \aligned alarms WP cannot
# translate ("\aligned not yet implemented"), which degenerate every goal
# in the TU (verify_all.sh:581-592).
WP_EXTRA_FLAGS = {"eval_alu": ["-no-warn-unaligned-pointer"],
                  "exec_alu": ["-no-warn-unaligned-pointer"]}

# Properties compile-gated OUT of the default build and proved by their
# own gated cell instead: -DALL_FIXES -DPROVE_OPTIMALITY. Mirrors the
# driver's SKIP_PROPS + `wp_pass <m> optimality` cells (verify_all.sh:
# 282-303 and, 381-410 mul, 480-498 apply_mask). Without this, report.py
# ran -wp-prop uopt against a TU where the preprocessor had removed the
# clause — a guaranteed non-green cell for the three hardest operators.
# The prop list per cell includes the witness stones: a stone assumes
# only the ones before it, so proving them all keeps every assumed fact
# a proved one (the driver's rationale, verify_all.sh:292-295).
OPT_GATED_PROPS = {"uopt", "sopt"}
OPT_CELLS = {
    "eval_and": (600, ["uopt", "sopt", "uopt_idem_max", "uopt_idem_min",
                       "sopt_half_max", "sopt_half_min", "sopt_rt_max",
                       "sopt_rt_min", "sopt_idem_max", "sopt_idem_min"]),
    "eval_mul": (900, ["uopt", "sopt", "uopt_wit_umax", "uopt_wit_umin",
                       "uopt_sum_umax", "uopt_sum_umin", "sopt_wit_smax",
                       "sopt_wit_smin", "sopt_pat_id", "sopt_sum_smax32",
                       "sopt_sum_smax64", "sopt_sum_smin"]),
    "eval_apply_mask": (600, ["uopt", "sopt"]),
}

# Files that must never enter a BMC translation unit: WP-only harnesses
# (no main, contract-only) and the composition experiment TUs. Without
# this every cbmc/esbmc invocation compiles them too (report.py's srcs is
# the whole corpus), which is at best wasted work and at worst a parse
# error attributed to the harness under test.
BMC_EXCLUDE_PAT = ("/exec_alu/", "/compose_try_")

# Bare BMC comment tags that name a PAIR of contract properties. Without
# the 'width' entry the bare `/* width */` tag used by 12 harnesses
# matched nothing and their uwidth/swidth BMC verdicts were silently
# dropped (2026-07-29 audit).
TAG_EXPAND = {"ord": ("uord", "sord"), "width": ("uwidth", "swidth"),
              "sound": ("usound", "ssound"), "opt": ("uopt", "sopt")}

# Supporting passes the certified driver runs that produce no per-property
# cell here. Surfaced in the HTML so a green matrix is never mistaken for
# the whole proof. (label, what it certifies, how to reproduce)
SUPPORTING_PASSES = [
    ("ACSL @lemma passes", "every lemma assumed inside the WP cells below "
     "(specs.h, shift-opt family, axioms_mul.h)",
     "./verify_all.sh  (specs.h/shift-opt/axioms_mul.h lemma cells)"),
    ("Helper contracts", "contract-annotated static helpers assumed at "
     "their call sites (mul_umask, mul_sext, mul_sext2, dm_sext, "
     "neg_sext, fi_sext)", "./verify_all.sh  (helpers cells)"),
    ("Side-goals per function", "stepping-stone asserts, assigns/frame, "
     "call preconditions, termination — everything not a named ensures",
     "./verify_all.sh  (side-goals cells)"),
    ("Executor agreement", "48 theorems: each bpf_exec.c ALU case-arm "
     "computes exactly the SEM_* semantics the validator abstracts",
     "./verify_all.sh --only exec_alu"),
    ("Axiom validation", "the trusted axiom families, by exhaustive ESBMC "
     "cells and brute-force enumeration (see docs/review_02 for tiers)",
     "cd axiom_validation && esbmc validate_specs_axioms.c --no-library "
     "--function <cell>"),
    ("Consistency probes", "per-TU \\false probes: WP must FAIL to prove "
     "them, i.e. the axiom base is not contradictory",
     "tests/consistency/probe_*.c"),
]

# Per-method WP -wp-timeout, mirroring verify_all.sh's per-harness ceilings
# (keep the two in sync). The global --timeout is only the FALLBACK, for a
# method not listed here and for the CBMC/ESBMC budgets. Without this, the
# slow WP goals (eval_add/eval_arsh usound ~19m, eval_lsh ~4m, eval_mul ~3m)
# spuriously time out under the 600s default and disagree with the driver.
WP_TIMEOUTS = {
    "eval_umax_bound": 20, "eval_smax_bound": 20,
    "eval_max_bound": 20, "eval_fill_max_bound": 20,
    "eval_umax_bits": 60, "eval_uand_max": 60, "eval_uor_max": 60,
    "eval_and": 600, "eval_or": 600, "eval_xor": 600,
    "eval_apply_mask": 600, "eval_sub": 600,
    "eval_rsh": 600,
    "eval_divmod": 300,
    "eval_defined": 20,
    "eval_fill_imm": 60,
    "eval_fill_imm64": 60,
    "eval_alu": 1200,
    "eval_arsh": 1800,
    "eval_add": 3000,
    # 2026-07-29 audit: these three had drifted BELOW the driver's
    # escalated ceilings (600/300/300), so certified-green goals rendered
    # as spurious timeouts. eval_lsh usound 10/11 + ssound 06/11 need
    # 1800 (verify_all.sh:547-551); eval_mul ssound part 18 is red at 300
    # and proves inside 900 (:366-383); eval_neg ssound is a ~15m search
    # that proves 1/1 isolated at 1200 (:429-436).
    "eval_lsh": 1800,
    "eval_mul": 900,
    "eval_neg": 1200,
}

# ---- HTML contract-table presentation (columns = properties) --------------
# Most-important-first: a reader should see soundness, then range
# well-formedness, then everything else. Unlisted props append alphabetically.
PROP_ORDER = [
    "usound", "ssound",
    "uopt", "sopt", "selfopt",
    "uord", "sord", "uwidth", "swidth",
    "agree_min", "agree_max", "valid", "type_ok",
    "err_iff", "err_frame",
    "frame", "err_def", "err_dom", "noerr",
    "const_u", "const_s", "def_iff",
    "unchanged_v", "unchanged_mask", "unchanged_s", "unchanged_u",
    "unchanged_size", "unchanged_buf", "mask_set", "mask_ok", "type_raw",
    "ufull", "umax_ok", "sfull32", "sfull64",
    "zero", "cover", "shape", "width", "half32", "half64", "optimal", "tight",
    "uand_nonneg", "uand_width", "uand_cover", "uand_half32", "uand_half64",
    "uor_nonneg", "uor_width", "uor_lb", "uor_cover", "uor_half32", "uor_half64",
    "umin64", "umax64", "uwiden32", "ukeep32",
    "smin32", "smax32", "smin64", "smax64",
]

# Column groups drive the show/hide toggles; "key" shows by default.
_KEY = {"usound", "ssound", "uopt", "sopt", "selfopt",
        "uord", "sord", "uwidth", "swidth",
        "agree_min", "agree_max", "valid", "type_ok"}
_STRUCT = {"unchanged_v", "unchanged_mask", "unchanged_s", "unchanged_u",
           "unchanged_size", "unchanged_buf", "mask_set", "mask_ok", "type_raw",
           "err_iff", "err_frame"}


def prop_group(p):
    return "key" if p in _KEY else "struct" if p in _STRUCT else "bounds"


def order_props(props):
    rank = {p: i for i, p in enumerate(PROP_ORDER)}
    return sorted(props, key=lambda p: (rank.get(p, len(PROP_ORDER)), p))


# One-line gloss shown under each column tag; it wraps, so the column stays
# narrow. Tags without an entry fall back to just the tag.
PROP_DESC = {
    "usound": "tracked unsigned range contains the true value, every input",
    "ssound": "tracked signed range contains the true value, every input",
    "uopt": "unsigned range is TIGHTEST: each endpoint attained (best abstract transformer)",
    "sopt": "signed range is TIGHTEST: each endpoint attained (best abstract transformer)",
    "selfopt": "output is self-optimal: each endpoint attained by a representable value",
    "uord": "unsigned range ordered (min ≤ max)",
    "sord": "signed range ordered (min ≤ max)",
    "uwidth": "unsigned range within the operand width",
    "swidth": "signed range within the operand width",
    "agree_min": "min agrees across signed/unsigned views",
    "agree_max": "max agrees across signed/unsigned views",
    "valid": "result is a well-formed register range",
    "type_ok": "argument type preserved (scalar/pointer)",
    "err_iff": "rejects exactly the constant-zero divisor",
    "err_frame": "register untouched when rejecting",
    "frame": "only the destination register changes",
    "err_def": "undefined operands are rejected",
    "err_dom": "errors only from undefined ops or div/mod-by-zero",
    "noerr": "well-formed non-div instructions are accepted",
    "const_u": "unsigned track pins the immediate pattern",
    "const_s": "signed track pins the canonical immediate",
    "def_iff": "error exactly iff a non-null operand is undefined",
    "unchanged_v": "value field unchanged",
    "unchanged_mask": "mask field unchanged",
    "unchanged_s": "signed range unchanged",
    "unchanged_u": "unsigned range unchanged",
    "unchanged_size": "size field unchanged",
    "unchanged_buf": "buffer-size field unchanged",
    "mask_set": "mask set to the operand width",
    "mask_ok": "mask is a supported width (32/64)",
    "type_raw": "result typed as a raw scalar",
    "ufull": "unsigned range set to full width [0, mask]",
    "umax_ok": "unsigned max is a supported width",
    "sfull32": "signed range set to [INT32_MIN, INT32_MAX]",
    "sfull64": "signed range set to [INT64_MIN, INT64_MAX]",
    "zero": "zero input yields a zero result",
    "cover": "result mask covers the input value",
    "shape": "result is an all-ones mask (2^k − 1)",
    "width": "result mask fits the operand width",
    "half32": "32-bit input under msk>>1 stays under msk>>1",
    "half64": "64-bit input under msk>>1 stays under msk>>1",
    "optimal": "result mask op-optimal (tightest 2^k − 1) for the input's bit-length",
    "tight": "result mask op-optimal for the input's bit-length (legacy label → optimal)",
    "uand_nonneg": "AND result is non-negative",
    "uand_width": "AND result within width",
    "uand_cover": "bounds a & b for all a≤v1, b≤v2",
    "uand_half32": "32-bit half-width propagates through AND",
    "uand_half64": "64-bit half-width propagates through AND",
    "uor_nonneg": "OR result is non-negative",
    "uor_width": "OR result within width",
    "uor_lb": "result is a lower bound on each input",
    "uor_cover": "bounds a | b for all a≤v1, b≤v2",
    "uor_half32": "32-bit half-width propagates through OR",
    "uor_half64": "64-bit half-width propagates through OR",
}

# Short gloss for the memory-safety table's category columns.
CAT_DESC = {
    "division": "no division by zero",
    "signed-overflow": "no signed integer overflow",
    "unsigned-overflow": "no unsigned wraparound",
    "shift": "no out-of-range / UB shift",
    "memory-leak": "no memory leak",
    "nan": "no NaN in float ops",
    "struct-fields": "struct field access in bounds",
    "data-races": "no data race",
    "deadlock": "no deadlock",
    "lock-order": "consistent lock order",
    "atomicity": "atomicity preserved",
}

#                 category            CBMC flag                    ESBMC flag                    WP -rte goal name
CATEGORIES = [
    ("bounds",            "--bounds-check",            "DEFAULT",                    "mem_access"),
    ("pointer",           "--pointer-check",           "DEFAULT",                    "mem_access"),
    ("division",          "--div-by-zero-check",       "DEFAULT",                    "division_by_zero"),
    ("signed-overflow",   "--signed-overflow-check",   "--overflow-check",           "signed_overflow"),
    ("unsigned-overflow", "--unsigned-overflow-check", "--unsigned-overflow-check",  None),
    ("shift",             "--undefined-shift-check",   "--ub-shift-check",           "shift"),
    ("memory-leak",       "--memory-leak-check",       "--memory-leak-check",        None),
    ("nan",               "--nan-check",               "--nan-check",                None),
    ("struct-fields",     None,                        "--struct-fields-check",      None),
    ("data-races",        None,                        "--data-races-check",         None),
    ("deadlock",          None,                        "--deadlock-check",           None),
    ("lock-order",        None,                        "--lock-order-check",         None),
    ("atomicity",         None,                        "--atomicity-check",          None),
]

# Categories whose FAIL is a documented design property, not a defect.
EXPECTED_FAIL = {"unsigned-overflow"}

# (method, prop) -> why this red is expected, filled during an 'original'
# run so the HTML can explain each '!' cell.
GATE_OF = {}
# (table, method, check) proved in the fixed-mode baseline, if one was
# supplied via --baseline. Empty means "no baseline": reds render plain.
EXPECTED_SET = set()


def expected_red(baseline_jsonl):
    """(method, prop) pairs that are EXPECTED to fail in 'original' mode.

    NOT derived from `#ifdef FIX_*` spans: this project keeps ONE contract
    of record and gates only function BODIES, so no ensures ever sits
    inside a gate (verified 2026-07-29 — zero matches corpus-wide). The
    truthful source is the fixed-mode baseline: a property PROVED under
    -DALL_FIXES but failing in the upstream port is exactly a documented
    defect the FIX repairs. A property failing in BOTH modes is not
    expected — it is a genuine gap, and must stay visibly red.

    Returns an empty map when no baseline is supplied, in which case every
    red renders as a plain red (understating, never overstating)."""
    if not baseline_jsonl or not os.path.exists(baseline_jsonl):
        return set()
    _meta, _props, _order, contract, safety, _t = load_jsonl(baseline_jsonl)
    good = set()
    for tbl, name in ((contract, "contract"), (safety, "memsafety")):
        for m, row in tbl.items():
            for k, triple in row.items():
                if any(v == OK for v in triple):
                    good.add((name, m, k))
    return good


def sh(cmd, timeout, dry=False):
    """Run cmd (list); return combined output text ('' on dry run).

    The child runs in its OWN PROCESS GROUP so a timeout kills the whole
    tree: frama-c spawns alt-ergo/z3/cvc5 children, and killing only the
    parent leaves them running — the orphaned-solver plague that starves
    later runs on this machine and produces phantom timeouts."""
    if dry:
        print("DRY:", " ".join(cmd), file=sys.stderr)
        return ""
    try:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True,
                             start_new_session=True)
    except FileNotFoundError:
        return "REPORT_PY_TOOL_MISSING"
    except OSError as exc:
        return "REPORT_PY_SPAWN_ERROR: %s" % exc
    try:
        return p.communicate(timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            p.kill()
        p.communicate()
        return "REPORT_PY_HARD_TIMEOUT"
    except KeyboardInterrupt:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            p.kill()
        raise


def discover_methods():
    out = []
    for bmc in sorted(glob.glob("harnesses/*/*_bmc.c")):
        m = os.path.basename(bmc)[:-len("_bmc.c")]
        impl = os.path.join(os.path.dirname(bmc), m + ".c")
        if os.path.exists(impl):
            out.append((m, impl, bmc))
    return out


# WP-ONLY harnesses: contract-only translation units with no BMC harness,
# which discover_methods() therefore cannot see. exec_alu holds the 48
# executor-agreement theorems — the result that ties the abstract
# transformers to the semantics DPDK actually runs — and was invisible in
# every report until 2026-07-29.
#   name -> (source, [(prop, gloss)], timeout, one-line description)
WP_ONLY = {
    "exec_alu": ("harnesses/exec_alu/exec_alu.c",
                 [("agree", "each bpf_exec.c ALU case-arm computes exactly "
                            "the SEM_* semantics the validator abstracts"),
                  ("frame", "the case-arm writes only the destination "
                            "register")],
                 120,
                 "executor agreement — 48 theorems over the interpreter's "
                 "ALU case-arms"),
}


def run_wp_only(name, prop, timeout, dry):
    """One WP-only harness pass. These have no -wp-fct target (the file is
    a family of small functions), so the property name selects the goals."""
    src, _, to, _ = (WP_ONLY[name][0], None, WP_ONLY[name][2], None)
    cmd = ["frama-c"] + ["-cpp-extra-args=" + d for d in DEFS] + \
          ["-rte", "-wp", "-wp-prover", WP_PROVERS, "-wp-par", str(NPAR),
           "-wp-timeout", str(to)] + WP_EXTRA_FLAGS.get(name, []) + \
          ["-wp-prop", prop, src]
    return wp_verdict(sh(cmd, to * 8 + 300, dry))


def harness_sources():
    """Implementation TUs for the BMC runs. Excludes _main/_bmc entry
    points and BMC_EXCLUDE_PAT (WP-only harnesses and experiment TUs):
    those have no BMC role, and compiling them into every cbmc/esbmc
    invocation is at best wasted work, at worst a parse error charged to
    whichever harness happens to be under test."""
    return sorted(f for f in glob.glob("harnesses/*/*.c")
                  if not f.endswith("_main.c") and not f.endswith("_bmc.c")
                  and not any(pat in "/" + f for pat in BMC_EXCLUDE_PAT))


def scan_deps(methods):
    """method -> set of methods its implementation #includes (callees)."""
    names = {m for m, _, _ in methods}
    deps = {}
    for m, impl, _ in methods:
        ds = set()
        for line in open(impl):
            inc = re.search(r'#\s*include\s+"[^"]*?(\w+)\.h"', line)
            if inc and inc.group(1) in names and inc.group(1) != m:
                ds.add(inc.group(1))
        deps[m] = ds
    return deps


def wp_sources(m, deps, impl_of):
    """Implementation files of m plus its transitive callees — the same
    per-harness translation unit verify_all.sh uses. Keeping this minimal
    matters beyond speed: an unrelated harness in the TU drags its scoped
    axioms (common/axioms_arsh.h) into every PO."""
    seen, stack = set(), [m]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(deps.get(cur, ()))
    return sorted(impl_of[x] for x in seen)


def dependency_order(methods):
    """Reorder methods bottom-up with dependency chains kept contiguous:
    first the shared foundations (methods that others depend on) by
    increasing chain depth, so e.g. eval_max_bound is immediately followed
    by eval_fill_max_bound; then the verification targets (methods nothing
    depends on), also by depth, so the deepest caller closes the report.
    A failure therefore always appears above every method that could
    inherit it. Dependencies are read from the #include "../<dep>/<dep>.h"
    lines in each implementation; ties break alphabetically. Falls back
    to alphabetical on a cycle."""
    names = {m for m, _, _ in methods}
    deps = scan_deps(methods)

    depth, visiting = {}, set()

    def d(m):
        if m in depth:
            return depth[m]
        if m in visiting:
            raise ValueError(m)
        visiting.add(m)
        depth[m] = 1 + max((d(x) for x in deps[m]), default=-1)
        visiting.discard(m)
        return depth[m]

    try:
        for m in names:
            d(m)
    except ValueError as cyc:
        print(f"report.py: dependency cycle at {cyc} — falling back to "
              "alphabetical", file=sys.stderr)
        return sorted(methods)

    has_dependents = {x for ds in deps.values() for x in ds}
    foundations = sorted((m for m in names if m in has_dependents),
                         key=lambda m: (depth[m], m))
    targets = sorted((m for m in names if m not in has_dependents),
                     key=lambda m: (depth[m], m))
    by_name = {m[0]: m for m in methods}
    return [by_name[m] for m in foundations + targets]


def ensures_of(impl):
    """Named ensures of the contract, DEDUPED. A FIX-gated contract states
    the same ensures name in both #ifdef branches; without the dedup the
    property is scheduled twice and burns two full ceilings (the driver
    hit this on apply_mask uopt — verify_all.sh:140-143)."""
    props, seen = [], set()
    for line in open(impl):
        if line.lstrip().startswith("//"):
            continue
        m = re.match(r"\s*ensures\s+(\w+)\s*:", line)
        if m and m.group(1) not in seen:
            seen.add(m.group(1))
            props.append(m.group(1))
    return props


def assert_map(bmc, props):
    """line number -> set of contract property names witnessed there.

    EVERY line of a multi-line assert statement maps to the statement's
    property set, not just its first line: CBMC reports the statement's
    first line but ESBMC can cite an interior line, and an unmapped
    citation used to make a real violation unattributable (which the
    ESBMC handler then rendered as a pass — review_03 finding A5).

    Bare pair-tags (`/* ord */`, `/* width */`, ...) expand through
    TAG_EXPAND; the bare `width` tag alone appears in 12 harnesses and
    matched nothing before 2026-07-29."""
    out = {}
    start, pending = None, set()
    for i, line in enumerate(open(bmc), 1):
        if line.lstrip().startswith("//"):
            continue
        if "assert(" in line and start is None:
            start = i
        if start is not None:
            comment = re.search(r"/\*(.*?)\*/", line)
            if comment:
                tokens = set(re.findall(r"\w+", comment.group(1)))
                for tag, pair in TAG_EXPAND.items():
                    if tag in tokens:
                        tokens |= set(pair)
                pending |= tokens & set(props)
            if ";" in line:
                if pending:
                    for ln in range(start, i + 1):
                        out[ln] = out.get(ln, set()) | pending
                start, pending = None, set()
    return out


# ---------------- WP ----------------

def wp_verdict(text, expect_goals=True):
    """Map a frama-c/WP run to a verdict glyph.

    ERROR is distinct from TIMEOUT and NA on purpose: a config/parse
    failure or a user error means the check did not happen, and letting
    that render as benign '-'/'T' hides real misconfiguration.

    `expect_goals` disambiguates "zero goals scheduled", which means two
    opposite things:
      True  (a NAMED ensures of the contract) — the clause should exist;
            zero goals means it was preprocessed away or misspelled, which
            the driver also scores FAILED. -> ERROR
      False (an -rte category like division_by_zero) — zero goals just
            means the function contains no such operation, which is
            genuinely not-applicable, not a problem. -> NA"""
    if "REPORT_PY_TOOL_MISSING" in text or "REPORT_PY_SPAWN_ERROR" in text:
        return ERROR
    if re.search(r"\[kernel\] User Error|\[wp\] User Error|syntax error", text):
        return ERROR
    if "No goal generated" in text:
        return ERROR if expect_goals else NA
    if "REPORT_PY_HARD_TIMEOUT" in text or "Timeout" in text:
        return TIMEOUT
    m = re.search(r"Proved goals:\s+(\d+)\s*/\s*(\d+)", text)
    if m:
        if int(m.group(2)) == 0:          # 0/0 — nothing was checked
            return ERROR if expect_goals else NA
        if m.group(1) == m.group(2):
            return OK
        return TIMEOUT     # WP does not refute; anything unproved is unknown
    return ERROR           # no result line at all: the run did not complete


def wp_cmd(method, prop, srcs, to, defs=None, split=None):
    """The frama-c command line for one property pass, mirroring the
    driver's per-function flags (WP_EXTRA_FLAGS) and parallelism."""
    cmd = ["frama-c"] + ["-cpp-extra-args=" + d for d in (
        defs if defs is not None else DEFS)]
    cmd += ["-rte", "-wp", "-wp-prover", WP_PROVERS, "-wp-par", str(NPAR),
            "-wp-timeout", str(to), "-wp-fct", method]
    cmd += WP_EXTRA_FLAGS.get(method, [])
    if split if split is not None else (
            method in WP_SPLIT_METHODS or
            prop in WP_SPLIT_PROPS.get(method, ())):
        cmd.append("-wp-split")
    return cmd + ["-wp-prop", prop] + srcs


def run_wp(method, prop, srcs, timeout, dry, expect_goals=True):
    """One property pass. PROVE_OPTIMALITY-gated properties get the
    driver's gated build instead of the default one — otherwise the
    preprocessor has deleted the very clause being requested."""
    if prop in OPT_GATED_PROPS and method in OPT_CELLS:
        return run_wp_optimality(method, prop, srcs, dry)
    to = WP_TIMEOUTS.get(method, timeout)
    # Wall cap: the per-goal ceiling times a generous multiple for a pass
    # that may schedule many goals, plus start-up. Kept well above to*3 so
    # a multi-goal pass is not guillotined mid-flight (its partial result
    # would be discarded entirely).
    return wp_verdict(sh(wp_cmd(method, prop, srcs, to), to * 8 + 300, dry),
                      expect_goals)


def run_wp_optimality(method, prop, srcs, dry):
    """uopt/sopt for the gated operators: -DALL_FIXES -DPROVE_OPTIMALITY,
    proving the property together with its witness stones (a stone assumes
    only the ones before it, so proving them all keeps every assumed fact
    a proved one — verify_all.sh:292-295). Only meaningful in fixed mode:
    the optimality clauses were derived under ALL_FIXES."""
    if MODE != "fixed":
        return NA
    to, props = OPT_CELLS[method]
    cmd = wp_cmd(method, ",".join(props), srcs, to,
                 defs=["-DALL_FIXES", "-DPROVE_OPTIMALITY"], split=False)
    return wp_verdict(sh(cmd, to * 8 + 300, dry))


# ---------------- CBMC ----------------

def run_cbmc_contract(method, bmc, srcs, props, amap, timeout, dry):
    stated = {p for v in amap.values() for p in v}
    text = sh(["cbmc"] + DEFS + [bmc] + srcs, timeout, dry)
    res = {p: NA for p in props}
    if "REPORT_PY_TOOL_MISSING" in text or "REPORT_PY_SPAWN_ERROR" in text:
        return {p: (ERROR if p in stated else NA) for p in props}
    if "REPORT_PY_HARD_TIMEOUT" in text:
        return {p: (TIMEOUT if p in stated else NA) for p in props}
    if re.search(r"^CONVERSION ERROR|PARSING ERROR|error:", text, re.M):
        return {p: (ERROR if p in stated else NA) for p in props}
    for line_no, verdict in re.findall(
            r"\[main\.assertion\.\d+\] line (\d+).*: (SUCCESS|FAILURE)", text):
        for p in amap.get(int(line_no), ()):
            # FAILURE is sticky: one violated assert for a property is a
            # counterexample regardless of its other asserts passing.
            if verdict == "FAILURE" or res[p] == NA:
                res[p] = OK if verdict == "SUCCESS" else FAIL
    return res


def run_bmc_flag(tool, flag, bmc, srcs, timeout, dry):
    cmd = [tool] + DEFS + ([flag] if flag and flag != "DEFAULT" else []) \
        + [bmc] + srcs
    if tool == "esbmc":
        cmd += ["--timeout", f"{timeout}s"]
    text = sh(cmd, timeout + 120, dry)
    if "REPORT_PY_TOOL_MISSING" in text:
        return NA
    if "VERIFICATION SUCCESSFUL" in text:
        return OK
    if "VERIFICATION FAILED" in text:
        return FAIL
    return TIMEOUT


# ---------------- ESBMC contract ----------------

def run_esbmc_contract(method, bmc, srcs, props, amap, timeout, dry):
    """ESBMC contract verdicts, FAIL-CLOSED.

    Previously, a run that printed VERIFICATION FAILED upgraded every
    stated property with no attributed violation to OK — so a violation
    cited outside the bmc file, or on an untagged/unmapped line, turned a
    RED run into an all-green row, in exactly the mode whose reds are the
    bug list (review_03 finding A5). Now an unattributable failure leaves
    the unattributed properties as ERROR: the run says something broke and
    the report must not claim otherwise."""
    text = sh(["esbmc"] + DEFS + ["--multi-property",
               "--timeout", f"{timeout}s", bmc] + srcs, timeout + 120, dry)
    stated = {p for v in amap.values() for p in v}
    res = {p: (NA if p not in stated else TIMEOUT) for p in props}
    if "REPORT_PY_TOOL_MISSING" in text or "REPORT_PY_SPAWN_ERROR" in text:
        return {p: (ERROR if p in stated else NA) for p in props}
    if re.search(r"PARSING ERROR|CONVERSION ERROR|error:", text):
        return {p: (ERROR if p in stated else NA) for p in props}
    if "VERIFICATION SUCCESSFUL" in text:
        return {p: (OK if p in stated else NA) for p in props}
    violated = set()
    attributed = False
    for f, line_no in re.findall(r"file (\S+) line (\d+)", text):
        if os.path.basename(f) == os.path.basename(bmc):
            hit = amap.get(int(line_no), set())
            violated |= hit
            attributed = attributed or bool(hit)
    if "VERIFICATION FAILED" in text:
        for p in stated:
            if p in violated:
                res[p] = FAIL
            elif attributed:
                # Some violation WAS attributed: properties not implicated
                # by any cited line genuinely held under --multi-property.
                res[p] = OK
            else:
                res[p] = ERROR   # failed, but nothing maps here — unknown
    return res


def bmc_sanity(bmc, srcs, timeout, dry):
    """Reachability leg: the harnesses carry `assert(0)` under -DBMC_SANITY
    after their preconditions, so a sanity run MUST be violated. If it is
    not, the preconditions are contradictory and every green BMC verdict
    for that harness is vacuous. Returns OK when the sanity assert is
    correctly refuted, FAIL when it is not, NA when the harness has no
    sanity leg."""
    if not any("BMC_SANITY" in line for line in open(bmc)):
        return NA
    text = sh(["cbmc"] + DEFS + ["-DBMC_SANITY", bmc] + srcs, timeout, dry)
    if "REPORT_PY" in text:
        return ERROR
    if "VERIFICATION FAILED" in text:
        return OK        # the unreachable-assert fired: preconditions live
    if "VERIFICATION SUCCESSFUL" in text:
        return FAIL      # nothing reached the assert: harness is vacuous
    return ERROR


# ---------------- render ----------------

def cell(c, e, w):
    return f"{c}·{e}·{w}"


def table(header, rows):
    line = "| " + " | ".join(header) + " |"
    sep = "|" + "|".join("---" for _ in header) + "|"
    body = ["| " + " | ".join(r) + " |" for r in rows]
    return "\n".join([line, sep] + body)


def tool_version(cmd):
    out = sh(cmd, 30)
    return out.strip().splitlines()[0] if out and "REPORT_PY" not in out else "not found"


LEGEND = ("Cell order: **CBMC · ESBMC · WP**. "
          "Glyphs: Y proved, X violated (counterexample), T timeout/unknown, "
          "! fails by design (intentional wraparound), "
          "E tool/config error (the check did not run), - not applicable.")


def platform_tag():
    return {"Darwin": "macos", "Linux": "linux"}.get(
        platform.system(), platform.system().lower())


def git_provenance():
    """branch @ short-hash (+dirty) of the tree that produced the run.
    Without this a screenshot cannot be tied to a state of the repo —
    the single most important thing to show beside a verification claim."""
    def g(*a):
        out = sh(["git"] + list(a), 15)
        return "" if "REPORT_PY" in out else out.strip()
    head = g("rev-parse", "--short", "HEAD")
    if not head:
        return "not a git tree"
    branch = g("rev-parse", "--abbrev-ref", "HEAD") or "?"
    dirty = " +dirty" if g("status", "--porcelain") else ""
    return f"{branch} @ {head}{dirty}"


def tally(contract, safety, cats):
    """Aggregate counts for the summary banner: per engine and overall,
    how many performed checks passed. NA cells are excluded (nothing was
    claimed); ERROR cells count as not-passed and are called out."""
    per = {t: {"good": 0, "run": 0} for t, _ in TOOLS}
    errors = 0
    for tbl, keys in ((contract, None), (safety, cats)):
        for m, row in tbl.items():
            for k, triple in row.items():
                if keys is not None and k not in keys:
                    continue
                for (tool, _), v in zip(TOOLS, triple):
                    if v == NA:
                        continue
                    per[tool]["run"] += 1
                    if v in GOOD:
                        per[tool]["good"] += 1
                    if v == ERROR:
                        errors += 1
    good = sum(p["good"] for p in per.values())
    run = sum(p["run"] for p in per.values())
    return per, good, run, errors


def environment():
    return [(name, tool_version(cmd)) for name, cmd in (
        ("frama-c", ["frama-c", "-version"]),
        ("cbmc", ["cbmc", "--version"]),
        ("esbmc", ["esbmc", "--version"]),
        ("z3", ["z3", "--version"]),
        ("alt-ergo", ["alt-ergo", "--version"]),
        ("host", ["uname", "-sm"]))]


def render_markdown(all_props, order, contract, safety, env, stamp="",
                    tag="", scope="full run", prov=""):
    cats = [c[0] for c in CATEGORIES]
    per, good, run, errors = tally(contract, safety, cats)
    c_rows = [[m] + [cell(*contract[m].get(p, (NA, NA, NA)))
                     for p in all_props] for m in order]
    s_rows = [[m] + [cell(*safety[m][c_]) for c_ in cats] for m in order]
    head = [f"# Verification results — {MODE}"]
    if scope != "full run":
        head.append(f"> **PARTIAL RUN — {scope}.** Not the full-corpus "
                    "report; do not read it as one.")
    head.append("**%d / %d checks passed** (%s)%s — mode `%s`, %s %s, tree "
                "`%s`." % (good, run,
                           " · ".join("%s %d/%d" % (e, per[t]["good"],
                                                    per[t]["run"])
                                      for t, e in TOOLS if per[t]["run"]),
                           f" — **{errors} error cells**" if errors else "",
                           MODE, stamp, tag, prov))
    sup = "\n".join("- **%s** — %s  \n  `%s`" % s for s in SUPPORTING_PASSES)
    return "\n\n".join(head + [
        LEGEND,
        "## Contract properties", table(["method"] + all_props, c_rows),
        "## Memory safety / UB checks", table(["method"] + cats, s_rows),
        "## Supporting passes (certified by verify_all.sh, not re-run here)",
        sup,
        "## Environment", "\n".join(f"- {k}: {v}" for k, v in env),
    ]) + "\n"


def section_bands(order, deps_map):
    """Label the first method of each structural section. `order` is the
    dependency order already computed by dependency_order(): foundations
    (methods others depend on) first, then verification targets."""
    has_dependents = {x for ds in deps_map.values() for x in ds}
    bands, seen_target = {}, False
    for i, m in enumerate(order):
        if i == 0:
            bands[m] = "Shared foundations — helpers other evaluators build on"
        elif m not in has_dependents and not seen_target:
            bands[m] = "Verification targets — operators and the dispatcher"
            seen_target = True
    return bands


class Sinks:
    """Stream results as they land, so `tail -f` shows live progress and an
    interrupted run still leaves valid partial files. Two granularities:
    the CSV row is the three-engine verdict per check (human/spreadsheet
    pivot); the JSONL record is atomic — one engine, one check, one
    verdict, with wall-clock seconds — preceded by one meta record."""

    def __init__(self, base, stamp, tag, env, scope="full run", prov=""):
        self.csv_f = open(base + ".csv", "w", newline="")
        self.csv = csv.writer(self.csv_f)
        self.csv_row(["method", "table", "check", "cbmc", "esbmc", "wp"])
        self.jsonl_f = open(base + ".jsonl", "w")
        # scope/git in the meta record so --render-from reproduces the
        # partial-run banner and provenance without guessing.
        self.event({"meta": True, "stamp": stamp, "platform": tag,
                    "mode": MODE, "env": dict(env), "scope": scope,
                    "git": prov})

    def event(self, obj):
        self.jsonl_f.write(json.dumps(obj) + "\n")
        self.jsonl_f.flush()

    def atomic(self, method, table, check, engine, verdict, seconds):
        self.event({"method": method, "table": table, "check": check,
                    "engine": engine, "verdict": verdict,
                    "seconds": seconds})

    def csv_row(self, cells):
        self.csv.writerow(cells)
        self.csv_f.flush()

    def close(self, env):
        for k, v in env:
            self.csv_row(["-", "environment", k, v, "", ""])
        self.csv_f.close()
        self.jsonl_f.close()


def timed(fn, *a):
    t0 = time.time()
    return fn(*a), round(time.time() - t0, 1)


ENG_IDX = {"cbmc": 0, "esbmc": 1, "wp": 2}


def load_jsonl(path):
    """Rebuild (meta, all_props, order, contract, safety, timings) from a
    run's jsonl. This is what makes presentation work free — every
    rendering change re-renders in under a second instead of costing
    another multi-hour verification run — and it is also what makes
    --resume possible: the jsonl is a complete, atomic record of which
    (method, table, check, engine) cells already have a verdict.

    `timings` maps (method, table, check, engine) -> seconds."""
    meta, contract, safety, timings = {}, {}, {}, {}
    order, all_props = [], []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue          # a run killed mid-write leaves a partial line
        if rec.get("meta"):
            meta = rec
            continue
        if "method" not in rec or "engine" not in rec:
            continue
        m, tbl, chk = rec["method"], rec["table"], rec["check"]
        eng, verdict = rec["engine"], rec["verdict"]
        timings[(m, tbl, chk, eng)] = rec.get("seconds", 0.0)
        if tbl == "sanity":
            continue          # recorded, but not a matrix cell
        if m not in order:
            order.append(m)
        store = contract if tbl == "contract" else safety
        row = store.setdefault(m, {})
        triple = list(row.get(chk, (NA, NA, NA)))
        triple[ENG_IDX[eng]] = verdict
        row[chk] = tuple(triple)
        if tbl == "contract" and chk not in all_props:
            all_props.append(chk)
    for m in order:
        contract.setdefault(m, {})
        safety.setdefault(m, {})
        for c_ in (c[0] for c in CATEGORIES):
            safety[m].setdefault(c_, (NA, NA, NA))
    return meta, all_props, order, contract, safety, timings


class Resume:
    """Verdicts carried over from a previous run's jsonl.

    Granularity is one (method, table, check, engine) cell, which matches
    how results are streamed. The BMC contract runs produce every property
    of a method in ONE invocation, so those are reused only when the whole
    set is present — a half-recorded method re-runs rather than reporting
    a mix of stale and fresh verdicts.

    Deliberately NOT invalidated by source mtime: a resumed run states in
    its scope line that it carries results from an earlier run, and the
    operator decides whether that is honest. Silently reusing verdicts
    across a source change would be worse than either alternative, so the
    banner always says how many cells were carried."""

    def __init__(self, path, mode):
        self.cells, self.timings, self.reused = {}, {}, 0
        self.path = path
        if not path:
            return
        meta, _p, _o, contract, safety, timings = load_jsonl(path)
        if meta.get("mode") and meta["mode"] != mode:
            raise SystemExit(
                f"--resume: {path} is a '{meta['mode']}' run but this is "
                f"'{mode}'. Refusing to mix modes in one report.")
        self.timings = timings
        for tbl, store in (("contract", contract), ("memsafety", safety)):
            for m, row in store.items():
                for chk, triple in row.items():
                    for eng, i in ENG_IDX.items():
                        if (m, tbl, chk, eng) in timings:
                            self.cells[(m, tbl, chk, eng)] = triple[i]

    def get(self, m, tbl, chk, eng):
        return self.cells.get((m, tbl, chk, eng))

    def seconds(self, m, tbl, chk, eng):
        return self.timings.get((m, tbl, chk, eng), 0.0)

    def all_props(self, m, tbl, props, eng):
        """The whole BMC batch for a method, or nothing."""
        if not props:
            return None
        got = {p: self.get(m, tbl, p, eng) for p in props}
        if any(v is None for v in got.values()):
            return None
        self.reused += len(got)
        return got

    def one(self, m, tbl, chk, eng):
        v = self.get(m, tbl, chk, eng)
        if v is not None:
            self.reused += 1
        return v


def write_delta(path, a_path, b_path):
    """The fixed-vs-original delta: only the cells whose verdict differs.
    In this project that difference IS the deliverable — each row is a
    property that the upstream code fails and the FIX_* repair recovers."""
    (ma, _, oa, ca, sa, _ta), (mb, _, ob, cb, sb, _tb) = (load_jsonl(a_path),
                                                          load_jsonl(b_path))
    la, lb = ma.get("mode", "A"), mb.get("mode", "B")
    rows = []
    for tbl_a, tbl_b, tname in ((ca, cb, "contract"), (sa, sb, "memsafety")):
        for m in sorted(set(tbl_a) | set(tbl_b)):
            keys = sorted(set(tbl_a.get(m, {})) | set(tbl_b.get(m, {})))
            for k in keys:
                va = tbl_a.get(m, {}).get(k, (NA, NA, NA))
                vb = tbl_b.get(m, {}).get(k, (NA, NA, NA))
                if va != vb:
                    rows.append((m, tname, k, va, vb))
    def chips(t):
        return "".join("<span class='v' style='background:%s' title='%s: %s'>"
                       "%s</span>" % (COLOR[v], eng, WORD[v], v)
                       for (_, eng), v in zip(TOOLS, t))
    body = "".join(
        "<tr><td class='m'>%s</td><td class='l'>%s</td><td class='l'>%s</td>"
        "<td>%s</td><td>%s</td></tr>" % (m, t, k, chips(va), chips(vb))
        for m, t, k, va, vb in rows)
    style = ("body{font:14px -apple-system,sans-serif;margin:2em;color:#1f2328}"
             "table{border-collapse:collapse}"
             "td,th{border:1px solid #d0d7de;padding:4px 8px;text-align:center}"
             "th.m,td.m{text-align:left;font-family:monospace}"
             "th.l,td.l{text-align:left}"
             ".v{display:inline-block;min-width:1.15em;padding:1px 3px;"
             "margin:0 .5px;border-radius:3px;color:#fff;"
             "font:600 12px monospace}"
             ".none{color:#57606a}")
    doc = ("<!doctype html><meta charset='utf-8'><title>Verification delta "
           f"{la} → {lb}</title><style>{style}</style>"
           f"<h1>Delta — <code>{la}</code> → <code>{lb}</code></h1>"
           "<p>Only cells whose verdict differs between the two runs. With "
           f"<code>{la}</code>=original and <code>{lb}</code>=fixed, each row "
           "is a property the upstream code does not satisfy and the "
           "corresponding <code>FIX_*</code> repair recovers — i.e. this "
           "table is the machine-checked bug list.</p>"
           + (f"<table><tr><th class='m'>method</th><th class='l'>table</th>"
              f"<th class='l'>check</th><th>{la}</th><th>{lb}</th></tr>"
              f"{body}</table>" if rows else
              "<p class='none'>No differing cells.</p>"))
    with open(path, "w") as f:
        f.write(doc)
    return len(rows)


COLOR = {OK: "#1a7f37", FAIL: "#cf222e", TIMEOUT: "#bf8700",
         EXPECTED: "#8250df", NA: "#8b949e", ERROR: "#6e2f8e"}
WORD = {OK: "proved", FAIL: "violated (counterexample)",
        TIMEOUT: "timeout / unknown", EXPECTED: "fails by design",
        NA: "not applicable", ERROR: "tool/config error — check did not run"}
# Verdicts that mean "a check really happened and passed" — the numerator
# of every count shown in the summary banner.
GOOD = {OK, EXPECTED}


TOOLS = (("cbmc", "CBMC"), ("esbmc", "ESBMC"), ("wp", "WP"))


def _colcls(k, group):
    """CSS classes for column k: c-<k> (per-column) + g-<group> (toggle)."""
    g = group(k) if group else ""
    return "c-%s%s" % (k, (" g-%s" % g) if g else "")


def html_table(keys, order, data, default=None, descs=None, group=None,
               bands=None):
    """One matrix. `bands` maps a method name to a section label; when a
    method carries one, a full-width band row is emitted before it, so the
    foundations / operators / dispatcher structure the dependency order
    already computes is visible instead of implied."""
    descs = descs or {}
    bands = bands or {}
    head = []
    for k in keys:
        d = descs.get(k, "")
        sub = '<div class="desc">%s</div>' % d if d else ""
        head.append('<th class="%s" title="%s"><div class="tag">%s</div>%s</th>'
                    % (_colcls(k, group), d or k, k, sub))
    rows = []
    for m in order:
        if m in bands:
            rows.append("<tr class='band'><td colspan='%d'>%s</td></tr>"
                        % (len(keys) + 2, bands[m]))
        cells, good, run = [], 0, 0
        for k in keys:
            triple = data[m].get(k, default) if default else data[m][k]
            for v in triple:
                if v != NA:
                    run += 1
                    good += v in GOOD
            gate = GATE_OF.get((m, k))
            spans = "".join(
                '<span class="v t-%s" style="background:%s" title="%s: %s%s">%s</span>'
                % (tool, COLOR[v], eng, WORD[v],
                   (" — gated by %s (documented upstream defect)" % gate)
                   if gate and v == EXPECTED else "", v)
                for (tool, eng), v in zip(TOOLS, triple))
            cells.append('<td class="%s"%s>%s</td>'
                         % (_colcls(k, group),
                            (" title='expected: %s'" % gate) if gate else "",
                            spans))
        # data-state drives the failures-first filter without any JS state
        state = "clean" if good == run else "dirty"
        rows.append("<tr data-state='%s'><td class='m'>%s</td>%s"
                    "<td class='n'>%d/%d</td></tr>"
                    % (state, m, "".join(cells), good, run))
    return ("<table><tr><th class='m'>method</th>%s"
            "<th class='n' title='checks passed / checks run in this row'>"
            "row</th></tr>%s</table>" % ("".join(head), "".join(rows)))


def html_legend():
    """A PERMANENT legend. Tooltips do not survive a screenshot, and every
    slide made from this report needs its glyphs readable on their own."""
    items = "".join(
        "<span class='li'><span class='v' style='background:%s'>%s</span>"
        "%s</span>" % (COLOR[g], g, WORD[g])
        for g in (OK, FAIL, TIMEOUT, EXPECTED, ERROR, NA))
    return ("<div class='legend'><b>Each cell:</b> three independent "
            "engines, in order <b>CBMC · ESBMC · WP</b>. %s</div>" % items)


def html_banner(stamp, tag, env, per, good, run, errors, scope, prov):
    """The one-shot summary: what was checked, how much passed, on which
    tree, in which mode. Designed to be screenshotted alone."""
    pct = (100.0 * good / run) if run else 0.0
    cls = "ok" if good == run and run else ("warn" if not errors else "err")
    engines = " · ".join(
        "%s %d/%d" % (eng, per[t]["good"], per[t]["run"])
        for t, eng in TOOLS if per[t]["run"])
    err = (" · <b class='errtag'>%d error cell%s</b>"
           % (errors, "" if errors == 1 else "s")) if errors else ""
    return (
        "<div class='banner %s'>"
        "<div class='big'>%d / %d checks passed <span class='pct'>(%.1f%%)</span></div>"
        "<div class='sub'>%s%s</div>"
        "<div class='sub'>mode <b>%s</b> · %s · %s · %s</div>"
        "<div class='sub prov'>%s</div>"
        "</div>" % (cls, good, run, pct, engines, err, MODE, stamp, tag,
                    scope, prov))


def margin_rows(timings, fallback_timeout):
    """WP cells ranked by how close their wall time ran to the configured
    per-goal ceiling.

    CAVEAT, stated in the rendered table too: the recorded seconds are the
    WALL TIME OF THE WHOLE PASS, which may schedule many goals, while the
    ceiling is PER GOAL. So a high ratio does not prove any single goal
    came close to timing out — it is a pointer at where the margin is
    thin and a re-measurement is worth doing. Cells at or above 1.0 are
    passes whose total exceeded a single goal's budget, which for a
    one-goal property IS a genuine near-miss."""
    rows = []
    for (m, tbl, chk, eng), secs in timings.items():
        if eng != "wp" or not secs:
            continue
        ceiling = WP_TIMEOUTS.get(m, fallback_timeout)
        if m in OPT_CELLS and chk in OPT_GATED_PROPS:
            ceiling = OPT_CELLS[m][0]
        rows.append((secs / ceiling, m, tbl, chk, secs, ceiling))
    rows.sort(reverse=True)
    return rows


def html_margins(timings, fallback_timeout, limit=15):
    rows = margin_rows(timings, fallback_timeout)
    if not rows:
        return ""
    hot = sum(1 for r in rows if r[0] >= 0.5)
    body = "".join(
        "<tr><td class='m'>%s</td><td class='l'>%s</td><td>%.0fs</td>"
        "<td>%ds</td><td class='%s'>%.0f%%</td></tr>"
        % (m, chk, secs, ceiling,
           "hot" if ratio >= 0.5 else "", 100 * ratio)
        for ratio, m, _tbl, chk, secs, ceiling in rows[:limit])
    return (
        "<h2>Timing margins <span class='note'>(WP cells, slowest first)"
        "</span></h2>"
        "<p class='note'>Wall time of each property pass against its "
        "configured per-goal ceiling. The pass may schedule many goals, so "
        "a high ratio is a pointer at thin margin rather than proof that a "
        "single goal nearly timed out — but it is where a green result is "
        "most likely to flip on a busier machine. "
        "<b>%d of %d WP cells ran at or above 50%% of ceiling.</b></p>"
        "<table><tr><th class='m'>method</th><th class='l'>property</th>"
        "<th>elapsed</th><th>ceiling</th><th>margin used</th></tr>%s</table>"
        % (hot, len(rows), body))


def html_supporting():
    """Everything the driver proves that has no cell in these tables. A
    green matrix without this section over-claims by omission."""
    rows = "".join(
        "<tr><td class='m'>%s</td><td class='l'>%s</td>"
        "<td class='l mono'>%s</td></tr>" % (name, what, how)
        for name, what, how in SUPPORTING_PASSES)
    return ("<h2>Supporting passes <span class='note'>(certified by "
            "verify_all.sh; not re-run by this report — every WP verdict "
            "above depends on them)</span></h2>"
            "<table class='sup'><tr><th class='m'>pass</th>"
            "<th class='l'>what it certifies</th>"
            "<th class='l'>reproduce</th></tr>%s</table>" % rows)


def write_html(path, all_props, order, contract, safety, env, stamp, tag,
               scope="full run", prov="", bands=None, timings=None,
               fallback_timeout=600):
    cats = [c[0] for c in CATEGORIES]
    per, good, run, errors = tally(contract, safety, cats)
    style = (
        "body{font:14px -apple-system,sans-serif;margin:0 2em 2em;color:#1f2328}"
        # fixed layout so every property column is the same width regardless
        # of its header text; the width fits the three boxes and the header
        # tag/description wrap into it.
        "table{border-collapse:collapse;margin:1em 0;table-layout:fixed}"
        "td,th{border:1px solid #d0d7de;padding:3px 4px;text-align:center}"
        "td{white-space:nowrap}"          # boxes stay on one row
        "th{background:#f6f8fa;vertical-align:top;white-space:normal;"
        "overflow-wrap:anywhere;position:sticky;top:var(--stick);z-index:2}"
        "th.c-bounds,th.c-pointer,th[class*=c-]{width:4.8em}"
        "th.m,td.m{text-align:left;font-family:monospace;white-space:nowrap;"
        "width:13em}"
        # method column sticks horizontally so a wide table stays readable
        # while scrolled — and so a crop keeps its row labels.
        "th.m{left:0;z-index:3}td.m{position:sticky;left:0;background:#fff;"
        "z-index:1}"
        "th.n,td.n{width:4.2em;font:600 11px monospace;color:#57606a}"
        "th.l,td.l{text-align:left;white-space:normal;width:auto}"
        "td.mono{font-family:monospace;font-size:11px;color:#57606a}"
        "th .tag{font:600 11px monospace}"
        "th .desc{font-weight:400;font-size:9.5px;color:#57606a;"
        "line-height:1.2;margin-top:2px}"
        ".v{display:inline-block;min-width:1.15em;padding:1px 2px;margin:0 .5px;"
        "border-radius:3px;color:#fff;font:600 11px monospace}"
        "tr.band td{background:#eef1f4;text-align:left;font:600 11px "
        "-apple-system,sans-serif;letter-spacing:.06em;text-transform:uppercase;"
        "color:#57606a;padding:6px 8px}"
        ".controls{position:sticky;top:0;background:#fff;padding:10px 0;"
        "border-bottom:1px solid #d0d7de;z-index:4;font-size:13px}"
        ".controls b{margin-left:14px}.controls b:first-child{margin-left:0}"
        ".controls button{margin:0 3px;cursor:pointer;padding:2px 8px}"
        ".controls label{margin:0 4px;white-space:nowrap;cursor:pointer}"
        # permanent legend — screenshots lose tooltips
        ".legend{font-size:12px;color:#57606a;padding:8px 0;line-height:2}"
        ".legend .li{margin-right:14px;white-space:nowrap}"
        ".legend .li .v{margin-right:4px}"
        # summary banner: the single screenshot that states the result
        ".banner{border:1px solid #d0d7de;border-left-width:6px;"
        "border-radius:6px;padding:12px 16px;margin:14px 0;background:#f6f8fa}"
        ".banner.ok{border-left-color:#1a7f37}"
        ".banner.warn{border-left-color:#bf8700}"
        ".banner.err{border-left-color:#6e2f8e}"
        ".banner .big{font-size:22px;font-weight:600}"
        ".banner .pct{font-weight:400;color:#57606a}"
        ".banner .sub{font-size:12.5px;color:#57606a;margin-top:3px}"
        ".banner .prov{font-family:monospace}"
        ".banner .errtag{color:#6e2f8e}"
        ".partial{border:1px solid #cf222e;background:#fff5f5;color:#82071e;"
        "border-radius:6px;padding:10px 14px;margin:14px 0;font-weight:600}"
        ".note{font-weight:400;font-size:12px;color:#57606a}"
        "td.hot{color:#bf8700;font-weight:600}"
        "h2{margin-top:1.6em}"
        # show/hide rules driven by <body> classes
        "body.h-key .g-key{display:none}body.h-struct .g-struct{display:none}"
        "body.h-bounds .g-bounds{display:none}"
        "body.h-cbmc .t-cbmc{display:none}body.h-esbmc .t-esbmc{display:none}"
        "body.h-wp .t-wp{display:none}"
        "body.only-fail tr[data-state=clean]{display:none}"
        # slide mode: bigger glyphs and type for projector screenshots
        "body.slide{font-size:17px}"
        "body.slide .v{min-width:1.5em;font-size:15px;padding:3px 5px}"
        "body.slide th .tag{font-size:14px}"
        "body.slide th .desc{font-size:12px}"
        "body.slide .banner .big{font-size:30px}"
        "body.slide td.m,body.slide th.m{font-size:15px;width:15em}"
        "@media print{.controls{position:static}"
        "body.h-struct .g-struct,body.h-bounds .g-bounds{display:none}}")
    controls = (
        '<div class="controls">'
        '<b>View:</b>'
        "<button onclick=\"preset('key')\">Key</button>"
        "<button onclick=\"preset('wp')\">WP-only</button>"
        "<button onclick=\"preset('all')\">All</button>"
        '<b>Columns:</b>'
        '<label><input type=checkbox id=g-key checked onchange=apply()>Key</label>'
        '<label><input type=checkbox id=g-struct onchange=apply()>Structural</label>'
        '<label><input type=checkbox id=g-bounds onchange=apply()>Bounds</label>'
        '<b>Tools:</b>'
        '<label><input type=checkbox id=t-cbmc checked onchange=apply()>CBMC</label>'
        '<label><input type=checkbox id=t-esbmc checked onchange=apply()>ESBMC</label>'
        '<label><input type=checkbox id=t-wp checked onchange=apply()>WP</label>'
        '<b>Rows:</b>'
        '<label><input type=checkbox id=only-fail onchange=apply()>'
        'Only rows with a non-pass</label>'
        '<b>Display:</b>'
        '<label><input type=checkbox id=slide onchange=apply()>'
        'Slide scale</label>'
        '</div>')
    js = (
        "<script>"
        "function ck(i){return document.getElementById(i).checked}"
        "function sv(i,v){document.getElementById(i).checked=v}"
        "function apply(){var b=document.body.classList;"
        "b.toggle('h-key',!ck('g-key'));b.toggle('h-struct',!ck('g-struct'));"
        "b.toggle('h-bounds',!ck('g-bounds'));b.toggle('h-cbmc',!ck('t-cbmc'));"
        "b.toggle('h-esbmc',!ck('t-esbmc'));b.toggle('h-wp',!ck('t-wp'));"
        "b.toggle('only-fail',ck('only-fail'));b.toggle('slide',ck('slide'));"
        "stick()}"
        # the sticky header must sit exactly below the sticky control bar,
        # whose height changes with slide mode and window width
        "function stick(){var c=document.querySelector('.controls');"
        "document.documentElement.style.setProperty('--stick',"
        "(c?c.offsetHeight:0)+'px')}"
        "window.addEventListener('resize',stick);"
        "function preset(p){"
        "var c={key:[1,0,0],wp:[1,0,0],all:[1,1,1]}[p];"
        "var t={key:[1,1,1],wp:[0,0,1],all:[1,1,1]}[p];"
        "sv('g-key',c[0]);sv('g-struct',c[1]);sv('g-bounds',c[2]);"
        "sv('t-cbmc',t[0]);sv('t-esbmc',t[1]);sv('t-wp',t[2]);apply()}"
        "</script>")
    partial = ("<div class='partial'>PARTIAL RUN — %s. This is not the "
               "full-corpus report; do not read it as one.</div>" % scope
               ) if scope != "full run" else ""
    mode_note = (
        "<p><b>Mode <code>fixed</code>:</b> every FIX_* repair enabled — this "
        "is the configuration the driver certifies green.</p>"
        if MODE == "fixed" else
        "<p><b>Mode <code>original</code>:</b> the faithful upstream port. "
        "Cells covered by a FIX_* gate are <b>expected</b> to be red here — "
        "that red set IS the upstream bug list, not a regression. Compare "
        "against the <code>fixed</code> report (or use "
        "<code>--delta</code>) to read it.</p>")
    doc = "".join([
        "<!doctype html><meta charset='utf-8'>",
        "<meta name='viewport' content='width=device-width,initial-scale=1'>",
        f"<title>Verification report {stamp} {tag} {MODE}</title>",
        f"<style>{style}</style>", js,
        '<body class="h-struct h-bounds" onload="apply()">',
        f"<h1>Verification results — {stamp} ({tag}, {MODE})</h1>",
        controls,
        partial,
        html_banner(stamp, tag, env, per, good, run, errors, scope, prov),
        html_legend(),
        mode_note,
        "<p>Each cell is three independent checks: <b>CBMC · ESBMC · WP</b> "
        "(WP is the deductive proof; the two BMC tools cross-check). Columns "
        "are ordered most-important-first; hover any value or column header "
        "for its meaning, and use the controls above to show/hide column "
        "groups or tools, filter to rows needing attention, or switch to "
        "slide scale for screenshots.</p>",
        "<h2>Contract properties</h2>",
        html_table(order_props(all_props), order, contract,
                   default=(NA, NA, NA), descs=PROP_DESC, group=prop_group,
                   bands=bands),
        "<h2>Memory safety / UB checks</h2>",
        html_table(cats, order, safety, descs=CAT_DESC, bands=bands),
        html_margins(timings or {}, fallback_timeout),
        html_supporting(),
        "<h2>Environment</h2><ul>",
        "".join(f"<li>{k}: {v}</li>" for k, v in env),
        f"<li>tree: {prov}</li><li>scope: {scope}</li>",
        "</ul></body>"])
    with open(path, "w") as f:
        f.write(doc)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument("mode", nargs="?", choices=("fixed", "original"),
                    default="original",
                    help="fixed: verify the FIX-gated semantics "
                         "(-DALL_FIXES); original (default): the faithful "
                         "upstream port, where FIX-gated goals are "
                         "expected to fail. Output files are suffixed "
                         "with the mode.")
    ap.add_argument("--outdir", default="reports",
                    help="report directory (default: reports/)")
    ap.add_argument("--timeout", type=int, default=600,
                    help="per-tool time budget in seconds (default 600); "
                         "WP gets it per prover per goal, CBMC/ESBMC per "
                         "run")
    ap.add_argument("--skip-wp", action="store_true",
                    help="skip the (slow) WP columns; cells show '-'")
    ap.add_argument("--skip-bmc", action="store_true",
                    help="skip the CBMC/ESBMC columns and the whole "
                         "memory-safety table; WP only")
    ap.add_argument("--methods", default=None,
                    help="comma-separated subset of methods to run")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the commands that would run, build no table")
    ap.add_argument("--render-from", metavar="JSONL", default=None,
                    help="re-render md/csv/html from a previous run's jsonl "
                         "without re-verifying anything (seconds, not hours)")
    ap.add_argument("--delta", nargs=2, metavar=("OLD_JSONL", "NEW_JSONL"),
                    default=None,
                    help="write the delta table between two runs "
                         "(original vs fixed = the upstream bug list)")
    ap.add_argument("--baseline", metavar="FIXED_JSONL", default=None,
                    help="in 'original' mode, a fixed-mode jsonl: cells it "
                         "proves but this run fails are marked '!' "
                         "(documented defect) instead of plain red")
    ap.add_argument("--resume", metavar="JSONL", default=None,
                    help="carry verdicts from an interrupted run's jsonl and "
                         "only compute what is missing; the report states "
                         "how many cells were carried")
    args = ap.parse_args()

    if args.delta:
        os.makedirs(args.outdir, exist_ok=True)
        out = os.path.join(args.outdir, "delta.html")
        n = write_delta(out, args.delta[0], args.delta[1])
        print(f"wrote {out} ({n} differing cells)", file=sys.stderr)
        return

    global MODE, DEFS, EXPECTED_SET
    MODE = args.mode
    DEFS = ["-DALL_FIXES"] if MODE == "fixed" else []
    if args.baseline and MODE == "original":
        EXPECTED_SET = expected_red(args.baseline)
        print(f"baseline: {len(EXPECTED_SET)} proved cells from "
              f"{args.baseline} — reds matching them render as '!'",
              file=sys.stderr)

    if args.render_from:
        (meta, all_props, order, contract, safety,
         timings) = load_jsonl(args.render_from)
        MODE = meta.get("mode", MODE)
        stamp = meta.get("stamp", "?")
        tag = meta.get("platform", platform_tag())
        env = list(meta.get("env", {}).items())
        # A jsonl written before scope/git were recorded cannot claim to be
        # a full run — say so rather than implying completeness.
        n_disc = len(discover_methods()) + len(WP_ONLY)
        scope = meta.get("scope") or (
            "scope not recorded in this jsonl (pre-2026-07-29 run); it "
            "covers %d of the %d harnesses now discoverable"
            % (len({r["method"] for r in map(json.loads, open(
                args.render_from)) if not r.get("meta")}), n_disc))
        prov = meta.get("git") or "not recorded in this jsonl"
        deps_map = scan_deps(discover_methods())
        base = os.path.join(args.outdir, f"{stamp}_{tag}_{MODE}")
        os.makedirs(args.outdir, exist_ok=True)
        with open(base + ".md", "w") as f:
            f.write(render_markdown(all_props, order, contract, safety, env,
                                    stamp, tag, scope, prov))
        write_html(base + ".html", all_props, order, contract, safety, env,
                   stamp, tag, scope, prov, section_bands(order, deps_map),
                   timings, args.timeout)
        print(f"re-rendered {base}.{{md,html}} from {args.render_from}",
              file=sys.stderr)
        return

    # deps/impl_of over ALL discovered methods, so wp_sources() can close
    # over callees even when --methods filters the iteration set.
    all_methods = discover_methods()
    deps = scan_deps(all_methods)
    impl_of = {m: impl for m, impl, _ in all_methods}

    methods = all_methods
    if args.methods:
        wanted = set(args.methods.split(","))
        methods = [m for m in methods if m[0] in wanted]
    methods = dependency_order(methods)
    srcs = harness_sources()
    if not methods:
        sys.exit("no matching harnesses/*/*_bmc.c found (run from formal/)")

    stamp = datetime.datetime.now().strftime("%Y-%m-%d_%H%M")
    tag = platform_tag()
    base = os.path.join(args.outdir, f"{stamp}_{tag}_{MODE}")
    env = environment()
    prov = git_provenance()
    # Run scope is recorded in the artifacts and gates the latest_* copy:
    # a subset run must never masquerade as the corpus-wide result.
    limits = []
    if args.methods:
        limits.append("%d of %d methods (--methods)"
                      % (len(methods), len(all_methods)))
    if args.skip_wp:
        limits.append("WP skipped")
    if args.skip_bmc:
        limits.append("CBMC/ESBMC skipped")
    resume = Resume(args.resume, MODE)
    # Coverage limits (which gate the latest_* copy) are kept separate from
    # provenance notes: a RESUMED run still covers the whole corpus, so it
    # is not "partial" — it just needs to say that some verdicts were
    # computed earlier.
    notes = []
    if args.resume:
        notes.append("resumed from %s (%d cells on file)"
                     % (os.path.basename(args.resume), len(resume.cells)))
    partial = bool(limits)
    scope = "; ".join(limits + notes) if (limits or notes) else "full run"
    # Timings of THIS run, plus any carried over, feed the margin table.
    timings = dict(resume.timings)
    sink = None
    if not args.dry_run:
        os.makedirs(args.outdir, exist_ok=True)
        gitignore = os.path.join(args.outdir, ".gitignore")
        if not os.path.exists(gitignore):
            with open(gitignore, "w") as f:
                f.write("# timestamped history stays local; latest.* is "
                        "tracked\n2*\n")
        sink = Sinks(base, stamp, tag, env, scope, prov)

    all_props, order = [], [m[0] for m in methods]
    contract, safety = {}, {}
    for m, impl, bmc in methods:
        props = ensures_of(impl)
        all_props += [p for p in props if p not in all_props]
        amap = assert_map(bmc, props)
        wsrcs = wp_sources(m, deps, impl_of)

        if args.skip_bmc:
            c, c_s = {p: NA for p in props}, 0.0
            e, e_s = {p: NA for p in props}, 0.0
        else:
            # BMC contract runs yield every property in ONE invocation, so
            # they are carried over only as a complete set.
            c = resume.all_props(m, "contract", props, "cbmc")
            if c is not None:
                c_s = resume.seconds(m, "contract", props[0], "cbmc")
                print(f"[{m}] contract: CBMC (resumed)", file=sys.stderr)
            else:
                print(f"[{m}] contract: CBMC", file=sys.stderr)
                c, c_s = timed(run_cbmc_contract, m, bmc, srcs, props, amap,
                               args.timeout, args.dry_run)
            e = resume.all_props(m, "contract", props, "esbmc")
            if e is not None:
                e_s = resume.seconds(m, "contract", props[0], "esbmc")
                print(f"[{m}] contract: ESBMC (resumed)", file=sys.stderr)
            else:
                print(f"[{m}] contract: ESBMC", file=sys.stderr)
                e, e_s = timed(run_esbmc_contract, m, bmc, srcs, props, amap,
                               args.timeout, args.dry_run)
            # Reachability leg: if the harness's preconditions are
            # contradictory, every green BMC verdict above is vacuous.
            sane = resume.one(m, "sanity", "bmc_reachable", "cbmc")
            if sane is not None:
                sane_s = resume.seconds(m, "sanity", "bmc_reachable", "cbmc")
            else:
                print(f"[{m}] contract: BMC sanity", file=sys.stderr)
                sane, sane_s = timed(bmc_sanity, bmc, srcs, args.timeout,
                                     args.dry_run)
            if sink:
                sink.atomic(m, "sanity", "bmc_reachable", "cbmc", sane, sane_s)
            if sane == FAIL:
                print(f"[{m}] WARNING: BMC sanity leg did not fire — the "
                      "harness preconditions may be unsatisfiable, making "
                      "its BMC verdicts vacuous", file=sys.stderr)
        w, w_s = {}, {}
        for p in props:
            cached = resume.one(m, "contract", p, "wp")
            if args.skip_wp:
                w[p], w_s[p] = NA, 0.0
            elif cached is not None:
                w[p] = cached
                w_s[p] = resume.seconds(m, "contract", p, "wp")
                print(f"[{m}] contract: WP {p} (resumed, {w[p]})",
                      file=sys.stderr)
            else:
                print(f"[{m}] contract: WP {p}", file=sys.stderr)
                w[p], w_s[p] = timed(run_wp, m, p, wsrcs, args.timeout,
                                     args.dry_run)
            timings[(m, "contract", p, "wp")] = w_s[p]
        # 'original' mode with a fixed-mode baseline: a property the FIXED
        # build proves but the upstream port does not is a DOCUMENTED
        # defect, not a regression. Mark it '!' so the red map separates
        # "the bug we are reporting" from "something is wrong".
        def mark(p, v):
            if MODE == "original" and v == FAIL and \
                    ("contract", m, p) in EXPECTED_SET:
                GATE_OF[(m, p)] = "proved under --fixes; fails upstream"
                return EXPECTED
            return v
        contract[m] = {p: (mark(p, c.get(p, NA)), mark(p, e.get(p, NA)),
                           mark(p, w.get(p, NA))) for p in props}
        if sink:
            for p in props:
                sink.atomic(m, "contract", p, "cbmc", c.get(p, NA), c_s)
                sink.atomic(m, "contract", p, "esbmc", e.get(p, NA), e_s)
                sink.atomic(m, "contract", p, "wp", w.get(p, NA), w_s[p])
                sink.csv_row([m, "contract", p, *contract[m][p]])

        safety[m] = {}
        esbmc_default = None
        wp_goal_cache = {}
        for cat, cflag, eflag, wgoal in CATEGORIES:
            print(f"[{m}] memsafety: {cat}", file=sys.stderr)
            cached_c = resume.one(m, "memsafety", cat, "cbmc")
            if cached_c is not None:
                cv, cv_s = cached_c, resume.seconds(m, "memsafety", cat, "cbmc")
            else:
                cv, cv_s = (timed(run_bmc_flag, "cbmc", cflag, bmc, srcs,
                                  args.timeout, args.dry_run)
                            if cflag and not args.skip_bmc else (NA, 0.0))
            cached_e = resume.one(m, "memsafety", cat, "esbmc")
            if cached_e is not None:
                ev, ev_s = cached_e, resume.seconds(m, "memsafety", cat,
                                                    "esbmc")
            elif args.skip_bmc:
                ev, ev_s = NA, 0.0
            elif eflag == "DEFAULT":
                if esbmc_default is None:
                    esbmc_default = timed(run_bmc_flag, "esbmc", None, bmc,
                                          srcs, args.timeout, args.dry_run)
                ev, ev_s = esbmc_default
            elif eflag:
                ev, ev_s = timed(run_bmc_flag, "esbmc", eflag, bmc, srcs,
                                 args.timeout, args.dry_run)
            else:
                ev, ev_s = NA, 0.0
            # 'bounds' and 'pointer' are BOTH WP's mem_access goal: run it
            # once per method, not once per category.
            cached_w = resume.one(m, "memsafety", cat, "wp")
            if args.skip_wp or not wgoal:
                wv, wv_s = NA, 0.0
            elif cached_w is not None:
                wv, wv_s = cached_w, resume.seconds(m, "memsafety", cat, "wp")
            elif wgoal in wp_goal_cache:
                wv, wv_s = wp_goal_cache[wgoal][0], 0.0
            else:
                # expect_goals=False: an -rte category with no goals means
                # the function has no such operation (no division, no
                # shift) — that is 'not applicable', not an error.
                wv, wv_s = timed(run_wp, m, wgoal, wsrcs, args.timeout,
                                 args.dry_run, False)
                wp_goal_cache[wgoal] = (wv, wv_s)
            if cat in EXPECTED_FAIL:
                cv = EXPECTED if cv == FAIL else cv
                ev = EXPECTED if ev == FAIL else ev
            safety[m][cat] = (cv, ev, wv)
            timings[(m, "memsafety", cat, "wp")] = wv_s
            if sink:
                sink.atomic(m, "memsafety", cat, "cbmc", cv, cv_s)
                sink.atomic(m, "memsafety", cat, "esbmc", ev, ev_s)
                sink.atomic(m, "memsafety", cat, "wp", wv, wv_s)
                sink.csv_row([m, "memsafety", cat, *safety[m][cat]])

    # WP-only harnesses (no BMC counterpart): appended as their own rows so
    # the executor-agreement track is visible in the matrix.
    for name, (src, cell_props, to, _desc) in WP_ONLY.items():
        if args.methods and name not in args.methods.split(","):
            continue
        if not os.path.exists(src):
            continue
        order.append(name)
        contract[name] = {}
        safety[name] = {c_[0]: (NA, NA, NA) for c_ in CATEGORIES}
        for prop, gloss in cell_props:
            PROP_DESC.setdefault(prop, gloss)
            if prop not in all_props:
                all_props.append(prop)
            cached = resume.one(name, "contract", prop, "wp")
            if args.skip_wp:
                v, v_s = NA, 0.0
            elif cached is not None:
                v, v_s = cached, resume.seconds(name, "contract", prop, "wp")
                print(f"[{name}] contract: WP {prop} (resumed, {v})",
                      file=sys.stderr)
            else:
                print(f"[{name}] contract: WP {prop}", file=sys.stderr)
                v, v_s = timed(run_wp_only, name, prop, args.timeout,
                               args.dry_run)
            contract[name][prop] = (NA, NA, v)
            timings[(name, "contract", prop, "wp")] = v_s
            if sink:
                sink.atomic(name, "contract", prop, "wp", v, v_s)
                sink.csv_row([name, "contract", prop, NA, NA, v])

    if args.dry_run:
        print("dry run complete — nothing written", file=sys.stderr)
        return

    sink.close(env)
    bands = section_bands(order, deps)
    with open(base + ".md", "w") as f:
        f.write(render_markdown(all_props, order, contract, safety, env,
                                stamp, tag, scope, prov))
    write_html(base + ".html", all_props, order, contract, safety, env,
               stamp, tag, scope, prov, bands, timings, args.timeout)
    # latest_<mode>.* is the artifact people link to and screenshot, so a
    # PARTIAL run must not overwrite it (that is exactly how the shipped
    # latest_fixed.html became a one-method file presented as the full
    # report). Partial runs land under latest_partial_<mode>.* instead.
    prefix = "latest_partial_" if partial else "latest_"
    for ext in (".md", ".csv", ".jsonl", ".html"):
        shutil.copyfile(base + ext,
                        os.path.join(args.outdir, f"{prefix}{MODE}" + ext))
    if partial:
        print(f"note: partial run ({scope}) — wrote {prefix}{MODE}.*, left "
              f"latest_{MODE}.* untouched", file=sys.stderr)
    if args.resume:
        print(f"resume: carried {resume.reused} cells from {args.resume}",
              file=sys.stderr)
    print(f"wrote {base}.{{md,csv,jsonl,html}} + {prefix}{MODE}.* "
          f"in {args.outdir}/", file=sys.stderr)


if __name__ == "__main__":
    main()
