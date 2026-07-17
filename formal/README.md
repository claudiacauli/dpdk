This folder contains the formal verification harnesses for the lib/bpf/bpf_validate.c code.

Developed with tool versions:
- frama-c 32.0 (Germanium)
- alt-ergo 2.6.2
- cvc5 1.3.2
- z3 4.15.4 (MacBook; the server runs 4.16.0 — prover-time on the
  cliff goals varies up to ~6x between the two, so keep timeout
  margins generous and re-check both machines after prover upgrades)

Trusted axioms: every `axiom` in the spec tree (shared ones under
`common/`, operator-specific ones next to their harness, e.g.
`harnesses/eval_mul/axioms_mul.h`, `harnesses/eval_divmod/axioms_div.h`)
covers a fact WP's SMT encoding cannot derive (bitwise AND, variable
shifts, multiplication, division). Each one is machine-validated over
its full instantiation domain, split by axiom class:

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
