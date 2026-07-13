This folder contains the formal verification harnesses for the lib/bpf/bpf_validate.c code.

Developed with tool versions:
- frama-c 32.0 (Germanium)
- alt-ergo 2.6.2
- cvc5 1.3.2
- z3 4.15.4 (MacBook; the server runs 4.16.0 — prover-time on the
  cliff goals varies up to ~6x between the two, so keep timeout
  margins generous and re-check both machines after prover upgrades)

Trusted axioms: every `axiom` in `common/specs.h` covers a fact WP's
SMT encoding cannot derive (bitwise AND, variable shifts). Each one is
proved over its full instantiation domain by CBMC:

    cd axiom_validation && cbmc validate_specs_axioms.c

must print VERIFICATION SUCCESSFUL. Re-run it (and extend it) whenever
an axiom is added or changed.
