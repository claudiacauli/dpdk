This folder contains the formal verification harnesses for the lib/bpf/bpf_validate.c code.

Two environment knobs on `verify_all.sh`, both defaulting to the
reference behaviour:

- `WP_PAR=n` — parallel prover tasks (default: one per physical core).
- `WP_TIMEOUT_PCT=n` — scale every `-wp-timeout` to n% of its written
  value (default 100).

Both are for adapting to a machine, never for changing what is claimed.
The ceilings in the script are calibrated to the reference box below;
`WP_TIMEOUT_PCT` exists so a faster or newer-toolchain machine can run
tighter without editing constants the reference box depends on. Measured
on a 2x EPYC 9454 server (96 physical cores, frama-c 33.0 / alt-ergo
2.6.3, cache-free, `WP_PAR=48`) on 2026-07-30:

- `eval_mul` `ssound` proves 77/77 at **every** ceiling from 30s to 900s,
  slowest goal 26.3s, wall-clock identical throughout — so there the
  ceiling only bounds the pathological case.
- That case is real: provers are tried IN TURN, each getting the full
  budget, so one goal whose first prover goes exponential costs 3x the
  ceiling. Two of five runs came in at ~970s = ~70s of work plus one
  full 900s budget.
- `WP_PAR` above 48 bought nothing (the run never saturated 48 — CPU/wall
  ratio 22.7), and prover ORDER changed neither wall-clock nor CPU.

Do not copy those numbers onto the reference box: there `eval_mul`
`ssound` part 18 is red at 300s and proves inside 900.

Developed with tool versions:
- frama-c 32.0 (Germanium)
- alt-ergo 2.6.2  (REQUIRED — see below)
- cvc5 1.3.2
- z3 4.15.4 (MacBook; the server runs 4.16.0 — prover-time on the
  cliff goals varies up to ~6x between the two, so keep timeout
  margins generous and re-check both machines after prover upgrades)

Alt-Ergo 2.6.x is load-bearing. The 2026-07-21 server sweep (96 cores,
frama-c 32.1, z3 4.16.0, cvc5 1.3.3, but alt-ergo 2.4.3-free) flipped
a consistent set of Mac-green goals red. Complete tally:
  - and.usound, or.uopt (monolithic, 10m spins)
  - most of eval_mul: uord, sord, 2 swidth parts, 30 usound parts,
    19 ssound parts, 4 optimality goals
  - rsh usound part3, ssound part3
  - arsh usound -5 parts, ssound -4, sopt part97, uopt 2 parts,
    17 shift_id side-goal parts
  - alu: swidth, sx_vld32, sx_vld64, ord_dx (uwidth proved but 16m)
All flips are Qed-milliseconds-then-spin with Alt-Ergo returning fast
[Failure]: true goals that only Alt-Ergo 2.6 closes. The MacBook set
above is the reference configuration for WP results; runs under older
Alt-Ergo are expected to show these reds. (Server lsh ssound also
printed FAILED (0/0) after a full 30m — no goal report at all, likely
an OOM/contention artifact from orphaned solvers of a killed earlier
run, not a proof result; recheck with
`./verify_all.sh --fixes --only eval_lsh --props ssound` on an idle
box before reading anything into it.)

Machine-dependent reds, confirmed pre-existing by A/B against
`git show HEAD:` on an idle machine (i.e. NOT regressions from the
optimality work). Diagnosed 2026-07-20:

  - `eval_lsh` `ssound` (parts 06, 11) — was a missing
    `lemmas_canon.h` include (`to_signed_canon_rt` is ssound
    load-bearing for every shift, see eval_rsh's note); FIXED.
  - `eval_lsh` `usound` (4 parts) — the widening branch's mask-strip;
    may simply need eval_arsh's 1800s ceiling instead of 600s.
  - `eval_arsh` `usound` — 96/97, one part just under the ceiling on
    this machine; server closes it.

Trusted axioms: every `axiom` in the spec tree (shared ones under
`common/`, operator-specific ones next to their harness, e.g.
`harnesses/eval_mul/axioms_mul.h`, `harnesses/eval_divmod/axioms_div.h`)
covers a fact WP's SMT encoding cannot derive (bitwise AND, variable
shifts, multiplication, division). Most are machine-validated over their
full instantiation domain, split by axiom class below — but NOT all, and
the exceptions are listed under "Validation tiers" after the commands.
(Corrected 2026-07-28: this section previously claimed "each one is
machine-validated over its full instantiation domain", which is false
for the tier-2 and tier-3 axioms below. Do not restore that wording.)

  - bitwise / wrap axioms (anything with & | ^ << >> or a to_uint64 wrap):

        cd axiom_validation && esbmc validate_specs_axioms.c --no-library

    must print VERIFICATION SUCCESSFUL (ESBMC's SMT bit-vector backend,
    ~15s; CBMC's SAT bit-blasting does not terminate on the 64-bit
    nonlinear checks — don't use it here).

  - nonlinear-integer axioms (pure arithmetic, no bitwise operator):

        cd axiom_validation && z3 mul_axioms_nia.smt2
        cd axiom_validation && z3 divmod_axioms_nia.smt2

    every check must print `unsat` (cvc5 --incremental agrees; each file
    asserts the axioms' negations over the unbounded integers).

Re-run (and extend) the relevant validator whenever an axiom is added or
changed — a false axiom silently invalidates every WP proof in the tree.

**Validation tiers.** Be precise about this when presenting the work; the
tiers are not equal evidence.

  - **Tier 1 — solver-proved over the full stated domain.** The great
    majority: the land/wrap/LenShift/ArshShift/ClzWindow/ApplyMaskBlocks/
    ShiftOptBranchSel families (ESBMC, bit-exact) and the MulBounds /
    DivModBounds arithmetic axioms (Z3+cvc5 over the *unbounded*
    integers, `*_nia.smt2`).
  - **Tier 2 — exhaustive small-width enumeration plus a width-uniform
    argument, because the full instance is intractable for every solver
    we have.** `mul_sext_congr` (`harnesses/eval_mul/axioms_mul.h`;
    w=4/8/12, `brute_sext_congr.c`) and `mul_ssound_overflow` /
    `mul_ssound_const` (`harnesses/eval_mul/eval_mul.h`; W=4/5,
    `brute_mul_lemmas.c`). The last two are the strongest assumptions in
    the tree: their conclusion IS `eval_mul_signed_soundness`, so
    eval_mul's signed soundness is ASSUMED on those branches, not
    derived. They were lemmas until 2026-07-28 and went red at 900s
    batched and 1800s isolated. ESBMC cells exist for all three but are
    server-tier (64-bit multipliers) and have not completed.
  - **Tier 3 — validated only over a sub-domain of what the axiom
    states.** `mul_mask_wrap` and the `exec_alu` LandMod/cast family are
    stated for unbounded integers but checked on uint64 (and one u128)
    instantiations.

`to_signed_pattern_id` and `land_absorb_window` (`common/axioms_and.h`)
had NO validation cell at all until the 2026-07-28 audit; cells were
added then (`land_and_canon_gaps` in `validate_specs_axioms.c`) and must
be run before the tiers above can be claimed complete.

**Consistency probes.** `tests/consistency/` holds one auto-generated
probe per translation unit, each including exactly that TU's header set
and asserting `lemma probe_false_<tu>: \false;`. WP must FAIL to prove
every one of them; a success would mean that TU's axiom set is
inconsistent and every proof discharged in it is worthless. Re-run after
adding any axiom.
