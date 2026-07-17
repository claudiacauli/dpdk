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
         - not applicable / no such check / property not stated

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
    run is dominated by the WP soundness goals — expect 10-30 minutes at
    the default --timeout 600.
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
import subprocess
import sys
import time

OK, FAIL, TIMEOUT, NA, EXPECTED = "Y", "X", "T", "-", "!"

WP_PROVERS = "alt-ergo,z3,cvc5"

# Set in main() from the positional mode argument ('fixed' | 'original').
MODE = "original"
DEFS = []

# Split-vs-monolith is a per-goal empirical choice measured in
# verify_all.sh (see its block comments); this mirrors the driver —
# keep the two in sync.
WP_SPLIT_METHODS = {"eval_lsh", "eval_rsh", "eval_arsh", "eval_and"}
WP_SPLIT_PROPS = {"eval_add": {"usound"}, "eval_or": {"ssound"},
                  "eval_xor": {"usound", "ssound"},
                  "eval_mul": {"usound", "ssound"}}

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
    "eval_lsh": 600, "eval_rsh": 600,
    "eval_mul": 300,
    "eval_divmod": 300,
    "eval_neg": 300,
    "eval_defined": 20,
    "eval_fill_imm": 60,
    "eval_fill_imm64": 60,
    "eval_alu": 1200,
    "eval_arsh": 1800,
    "eval_add": 3000,
}

# ---- HTML contract-table presentation (columns = properties) --------------
# Most-important-first: a reader should see soundness, then range
# well-formedness, then everything else. Unlisted props append alphabetically.
PROP_ORDER = [
    "usound", "ssound",
    "uord", "sord", "uwidth", "swidth",
    "agree_min", "agree_max", "valid", "type_ok",
    "err_iff", "err_frame",
    "frame", "err_def", "err_dom", "noerr",
    "const_u", "const_s", "def_iff",
    "unchanged_v", "unchanged_mask", "unchanged_s", "unchanged_u",
    "unchanged_size", "unchanged_buf", "mask_set", "mask_ok", "type_raw",
    "ufull", "umax_ok", "sfull32", "sfull64",
    "zero", "cover", "shape", "width", "half32", "half64", "tight",
    "uand_nonneg", "uand_width", "uand_cover", "uand_half32", "uand_half64",
    "uor_nonneg", "uor_width", "uor_lb", "uor_cover", "uor_half32", "uor_half64",
    "umin64", "umax64", "uwiden32", "ukeep32",
    "smin32", "smax32", "smin64", "smax64",
]

# Column groups drive the show/hide toggles; "key" shows by default.
_KEY = {"usound", "ssound", "uord", "sord", "uwidth", "swidth",
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
    "tight": "result mask tight for the input's bit-length",
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


def sh(cmd, timeout, dry=False):
    """Run cmd (list); return combined output text ('' on dry run)."""
    if dry:
        print("DRY:", " ".join(cmd), file=sys.stderr)
        return ""
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True, timeout=timeout)
        return p.stdout
    except subprocess.TimeoutExpired:
        return "REPORT_PY_HARD_TIMEOUT"
    except FileNotFoundError:
        return "REPORT_PY_TOOL_MISSING"


def discover_methods():
    out = []
    for bmc in sorted(glob.glob("harnesses/*/*_bmc.c")):
        m = os.path.basename(bmc)[:-len("_bmc.c")]
        impl = os.path.join(os.path.dirname(bmc), m + ".c")
        if os.path.exists(impl):
            out.append((m, impl, bmc))
    return out


def harness_sources():
    return sorted(f for f in glob.glob("harnesses/*/*.c")
                  if not f.endswith("_main.c") and not f.endswith("_bmc.c"))


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
    props = []
    for line in open(impl):
        if line.lstrip().startswith("//"):
            continue
        m = re.match(r"\s*ensures\s+(\w+)\s*:", line)
        if m:
            props.append(m.group(1))
    return props


def assert_map(bmc, props):
    """line number (of the assert statement) -> set of contract property
    names it witnesses. The /* name */ comment may sit on any line of a
    multi-line assert; it is attributed to the statement's first line,
    which is the line CBMC/ESBMC report."""
    out = {}
    start = None
    for i, line in enumerate(open(bmc), 1):
        if line.lstrip().startswith("//"):
            continue
        if "assert(" in line:
            start = i
        if start is not None:
            comment = re.search(r"/\*(.*?)\*/", line)
            if comment:
                tokens = set(re.findall(r"\w+", comment.group(1)))
                if "ord" in tokens:
                    tokens |= {"uord", "sord"}
                hit = tokens & set(props)
                if hit:
                    out[start] = out.get(start, set()) | hit
            if ";" in line:
                start = None
    return out


# ---------------- WP ----------------

def wp_verdict(text):
    if "REPORT_PY_TOOL_MISSING" in text:
        return NA
    if "No goal generated" in text:
        return NA
    if "REPORT_PY_HARD_TIMEOUT" in text or "Timeout" in text:
        return TIMEOUT
    m = re.search(r"Proved goals:\s+(\d+)\s*/\s*(\d+)", text)
    if m and m.group(1) == m.group(2) and int(m.group(1)) > 0:
        return OK
    return TIMEOUT  # WP does not refute; anything unproved is 'unknown'


def run_wp(method, prop, srcs, timeout, dry):
    # Per-method ceiling (mirrors verify_all.sh); the passed --timeout is the
    # fallback for any method not in the map.
    to = WP_TIMEOUTS.get(method, timeout)
    cmd = ["frama-c"] + ["-cpp-extra-args=" + d for d in DEFS] + \
          ["-rte", "-wp", "-wp-prover", WP_PROVERS,
           "-wp-timeout", str(to), "-wp-fct", method]
    if method in WP_SPLIT_METHODS or prop in WP_SPLIT_PROPS.get(method, ()):
        cmd.append("-wp-split")
    cmd += ["-wp-prop", prop] + srcs
    return wp_verdict(sh(cmd, to * 3 + 120, dry))


# ---------------- CBMC ----------------

def run_cbmc_contract(method, bmc, srcs, props, amap, timeout, dry):
    text = sh(["cbmc"] + DEFS + [bmc] + srcs, timeout, dry)
    res = {p: NA for p in props}
    if "REPORT_PY_TOOL_MISSING" in text:
        return res
    if "REPORT_PY_HARD_TIMEOUT" in text:
        return {p: (TIMEOUT if any(p in v for v in amap.values()) else NA)
                for p in props}
    for line_no, verdict in re.findall(
            r"\[main\.assertion\.\d+\] line (\d+).*: (SUCCESS|FAILURE)", text):
        for p in amap.get(int(line_no), ()):
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
    text = sh(["esbmc"] + DEFS + ["--multi-property",
               "--timeout", f"{timeout}s", bmc] + srcs, timeout + 120, dry)
    stated = {p for v in amap.values() for p in v}
    res = {p: (NA if p not in stated else TIMEOUT) for p in props}
    if "REPORT_PY_TOOL_MISSING" in text:
        return {p: NA for p in props}
    if "VERIFICATION SUCCESSFUL" in text:
        return {p: (OK if p in stated else NA) for p in props}
    violated = set()
    for f, line_no in re.findall(r"file (\S+) line (\d+)", text):
        if os.path.basename(f) == os.path.basename(bmc):
            violated |= amap.get(int(line_no), set())
    if "VERIFICATION FAILED" in text:
        for p in stated:
            res[p] = FAIL if p in violated else OK
    return res


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
          "! fails by design (intentional wraparound), - not applicable.")


def platform_tag():
    return {"Darwin": "macos", "Linux": "linux"}.get(
        platform.system(), platform.system().lower())


def environment():
    return [(name, tool_version(cmd)) for name, cmd in (
        ("frama-c", ["frama-c", "-version"]),
        ("cbmc", ["cbmc", "--version"]),
        ("esbmc", ["esbmc", "--version"]),
        ("z3", ["z3", "--version"]),
        ("alt-ergo", ["alt-ergo", "--version"]),
        ("host", ["uname", "-sm"]))]


def render_markdown(all_props, order, contract, safety, env):
    cats = [c[0] for c in CATEGORIES]
    c_rows = [[m] + [cell(*contract[m].get(p, (NA, NA, NA)))
                     for p in all_props] for m in order]
    s_rows = [[m] + [cell(*safety[m][c_]) for c_ in cats] for m in order]
    return "\n\n".join([
        f"# Verification results — {MODE}", LEGEND,
        "## Contract properties", table(["method"] + all_props, c_rows),
        "## Memory safety / UB checks", table(["method"] + cats, s_rows),
        "## Environment", "\n".join(f"- {k}: {v}" for k, v in env),
    ]) + "\n"


class Sinks:
    """Stream results as they land, so `tail -f` shows live progress and an
    interrupted run still leaves valid partial files. Two granularities:
    the CSV row is the three-engine verdict per check (human/spreadsheet
    pivot); the JSONL record is atomic — one engine, one check, one
    verdict, with wall-clock seconds — preceded by one meta record."""

    def __init__(self, base, stamp, tag, env):
        self.csv_f = open(base + ".csv", "w", newline="")
        self.csv = csv.writer(self.csv_f)
        self.csv_row(["method", "table", "check", "cbmc", "esbmc", "wp"])
        self.jsonl_f = open(base + ".jsonl", "w")
        self.event({"meta": True, "stamp": stamp, "platform": tag,
                    "mode": MODE, "env": dict(env)})

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


COLOR = {OK: "#1a7f37", FAIL: "#cf222e", TIMEOUT: "#bf8700",
         EXPECTED: "#8250df", NA: "#8b949e"}
WORD = {OK: "proved", FAIL: "violated (counterexample)",
        TIMEOUT: "timeout / unknown", EXPECTED: "fails by design",
        NA: "not applicable"}


TOOLS = (("cbmc", "CBMC"), ("esbmc", "ESBMC"), ("wp", "WP"))


def _colcls(k, group):
    """CSS classes for column k: c-<k> (per-column) + g-<group> (toggle)."""
    g = group(k) if group else ""
    return "c-%s%s" % (k, (" g-%s" % g) if g else "")


def html_table(keys, order, data, default=None, descs=None, group=None):
    descs = descs or {}
    head = []
    for k in keys:
        d = descs.get(k, "")
        sub = '<div class="desc">%s</div>' % d if d else ""
        head.append('<th class="%s" title="%s"><div class="tag">%s</div>%s</th>'
                    % (_colcls(k, group), d or k, k, sub))
    rows = []
    for m in order:
        cells = []
        for k in keys:
            triple = data[m].get(k, default) if default else data[m][k]
            spans = "".join(
                '<span class="v t-%s" style="background:%s" title="%s: %s">%s</span>'
                % (tool, COLOR[v], eng, WORD[v], v)
                for (tool, eng), v in zip(TOOLS, triple))
            cells.append('<td class="%s">%s</td>' % (_colcls(k, group), spans))
        rows.append("<tr><td class='m'>%s</td>%s</tr>" % (m, "".join(cells)))
    return ("<table><tr><th class='m'>method</th>%s</tr>%s</table>"
            % ("".join(head), "".join(rows)))


def write_html(path, all_props, order, contract, safety, env, stamp, tag):
    cats = [c[0] for c in CATEGORIES]
    style = (
        "body{font:14px -apple-system,sans-serif;margin:0 2em 2em;color:#1f2328}"
        # fixed layout so every property column is the same width regardless
        # of its header text; the width fits the three boxes and the header
        # tag/description wrap into it.
        "table{border-collapse:collapse;margin:1em 0;table-layout:fixed}"
        "td,th{border:1px solid #d0d7de;padding:3px 4px;text-align:center}"
        "td{white-space:nowrap}"          # boxes stay on one row
        "th{background:#f6f8fa;vertical-align:top;white-space:normal;"
        "overflow-wrap:anywhere}"          # long tags/sentences wrap in-column
        "th.col{width:4.8em}"              # uniform property-column width
        "th.m,td.m{text-align:left;font-family:monospace;white-space:nowrap;"
        "width:13em}"
        "th .tag{font:600 11px monospace}"
        "th .desc{font-weight:400;font-size:9.5px;color:#57606a;"
        "line-height:1.2;margin-top:2px}"
        ".v{display:inline-block;min-width:1.15em;padding:1px 2px;margin:0 .5px;"
        "border-radius:3px;color:#fff;font:600 11px monospace}"
        ".controls{position:sticky;top:0;background:#fff;padding:10px 0;"
        "border-bottom:1px solid #d0d7de;z-index:1;font-size:13px}"
        ".controls b{margin-left:14px}.controls b:first-child{margin-left:0}"
        ".controls button{margin:0 3px;cursor:pointer;padding:2px 8px}"
        ".controls label{margin:0 4px;white-space:nowrap;cursor:pointer}"
        # show/hide rules driven by <body> classes
        "body.h-key .g-key{display:none}body.h-struct .g-struct{display:none}"
        "body.h-bounds .g-bounds{display:none}"
        "body.h-cbmc .t-cbmc{display:none}body.h-esbmc .t-esbmc{display:none}"
        "body.h-wp .t-wp{display:none}")
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
        '</div>')
    js = (
        "<script>"
        "function ck(i){return document.getElementById(i).checked}"
        "function sv(i,v){document.getElementById(i).checked=v}"
        "function apply(){var b=document.body.classList;"
        "b.toggle('h-key',!ck('g-key'));b.toggle('h-struct',!ck('g-struct'));"
        "b.toggle('h-bounds',!ck('g-bounds'));b.toggle('h-cbmc',!ck('t-cbmc'));"
        "b.toggle('h-esbmc',!ck('t-esbmc'));b.toggle('h-wp',!ck('t-wp'))}"
        "function preset(p){"
        "var c={key:[1,0,0],wp:[1,0,0],all:[1,1,1]}[p];"
        "var t={key:[1,1,1],wp:[0,0,1],all:[1,1,1]}[p];"
        "sv('g-key',c[0]);sv('g-struct',c[1]);sv('g-bounds',c[2]);"
        "sv('t-cbmc',t[0]);sv('t-esbmc',t[1]);sv('t-wp',t[2]);apply()}"
        "</script>")
    doc = "".join([
        "<!doctype html><meta charset='utf-8'>",
        f"<title>Verification report {stamp} {tag} {MODE}</title>",
        f"<style>{style}</style>", js,
        '<body class="h-struct h-bounds" onload="apply()">',
        f"<h1>Verification results — {stamp} ({tag}, {MODE})</h1>",
        controls,
        "<p>Each cell is three independent checks: <b>CBMC · ESBMC · WP</b> "
        "(WP is the deductive proof; the two BMC tools cross-check). Columns "
        "are ordered most-important-first; hover any value or column header "
        "for its meaning, and use the controls above to show/hide column "
        "groups or tools.</p>",
        "<h2>Contract properties</h2>",
        html_table(order_props(all_props), order, contract,
                   default=(NA, NA, NA), descs=PROP_DESC, group=prop_group),
        "<h2>Memory safety / UB checks</h2>",
        html_table(cats, order, safety, descs=CAT_DESC),
        "<h2>Environment</h2><ul>",
        "".join(f"<li>{k}: {v}</li>" for k, v in env),
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
    ap.add_argument("--methods", default=None,
                    help="comma-separated subset of methods to run")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the commands that would run, build no table")
    args = ap.parse_args()

    global MODE, DEFS
    MODE = args.mode
    DEFS = ["-DALL_FIXES"] if MODE == "fixed" else []

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
    sink = None
    if not args.dry_run:
        os.makedirs(args.outdir, exist_ok=True)
        gitignore = os.path.join(args.outdir, ".gitignore")
        if not os.path.exists(gitignore):
            with open(gitignore, "w") as f:
                f.write("# timestamped history stays local; latest.* is "
                        "tracked\n2*\n")
        sink = Sinks(base, stamp, tag, env)

    all_props, order = [], [m[0] for m in methods]
    contract, safety = {}, {}
    for m, impl, bmc in methods:
        props = ensures_of(impl)
        all_props += [p for p in props if p not in all_props]
        amap = assert_map(bmc, props)
        wsrcs = wp_sources(m, deps, impl_of)

        print(f"[{m}] contract: CBMC", file=sys.stderr)
        c, c_s = timed(run_cbmc_contract, m, bmc, srcs, props, amap,
                       args.timeout, args.dry_run)
        print(f"[{m}] contract: ESBMC", file=sys.stderr)
        e, e_s = timed(run_esbmc_contract, m, bmc, srcs, props, amap,
                       args.timeout, args.dry_run)
        w, w_s = {}, {}
        for p in props:
            if args.skip_wp:
                w[p], w_s[p] = NA, 0.0
            else:
                print(f"[{m}] contract: WP {p}", file=sys.stderr)
                w[p], w_s[p] = timed(run_wp, m, p, wsrcs, args.timeout,
                                     args.dry_run)
        contract[m] = {p: (c.get(p, NA), e.get(p, NA), w.get(p, NA))
                       for p in props}
        if sink:
            for p in props:
                sink.atomic(m, "contract", p, "cbmc", c.get(p, NA), c_s)
                sink.atomic(m, "contract", p, "esbmc", e.get(p, NA), e_s)
                sink.atomic(m, "contract", p, "wp", w.get(p, NA), w_s[p])
                sink.csv_row([m, "contract", p, *contract[m][p]])

        safety[m] = {}
        esbmc_default = None
        for cat, cflag, eflag, wgoal in CATEGORIES:
            print(f"[{m}] memsafety: {cat}", file=sys.stderr)
            cv, cv_s = (timed(run_bmc_flag, "cbmc", cflag, bmc, srcs,
                              args.timeout, args.dry_run)
                        if cflag else (NA, 0.0))
            if eflag == "DEFAULT":
                if esbmc_default is None:
                    esbmc_default = timed(run_bmc_flag, "esbmc", None, bmc,
                                          srcs, args.timeout, args.dry_run)
                ev, ev_s = esbmc_default
            elif eflag:
                ev, ev_s = timed(run_bmc_flag, "esbmc", eflag, bmc, srcs,
                                 args.timeout, args.dry_run)
            else:
                ev, ev_s = NA, 0.0
            wv, wv_s = ((NA, 0.0) if (args.skip_wp or not wgoal)
                        else timed(run_wp, m, wgoal, wsrcs, args.timeout,
                                   args.dry_run))
            if cat in EXPECTED_FAIL:
                cv = EXPECTED if cv == FAIL else cv
                ev = EXPECTED if ev == FAIL else ev
            safety[m][cat] = (cv, ev, wv)
            if sink:
                sink.atomic(m, "memsafety", cat, "cbmc", cv, cv_s)
                sink.atomic(m, "memsafety", cat, "esbmc", ev, ev_s)
                sink.atomic(m, "memsafety", cat, "wp", wv, wv_s)
                sink.csv_row([m, "memsafety", cat, *safety[m][cat]])

    if args.dry_run:
        print("dry run complete — nothing written", file=sys.stderr)
        return

    sink.close(env)
    with open(base + ".md", "w") as f:
        f.write(render_markdown(all_props, order, contract, safety, env))
    write_html(base + ".html", all_props, order, contract, safety, env,
               stamp, tag)
    for ext in (".md", ".csv", ".jsonl", ".html"):
        shutil.copyfile(base + ext,
                        os.path.join(args.outdir, f"latest_{MODE}" + ext))
    print(f"wrote {base}.{{md,csv,jsonl,html}} + latest_{MODE}.* "
          f"in {args.outdir}/", file=sys.stderr)


if __name__ == "__main__":
    main()
