#ifndef AXIOMS_DIV_H
#define AXIOMS_DIV_H

#include "../../common/specs.h"

/*
 * Trusted axioms used ONLY by the eval_divmod proof, TU-scoped in the
 * harness folder like axioms_mul.h / axioms_clz.h (quantified axioms
 * perturb every PO in whose translation unit they appear — include from
 * eval_divmod.c only). Same trust contract as the rest of the tree:
 * every axiom is machine-validated over its full domain before use —
 * the pure div/mod arithmetic by an NIA solver
 * (axiom_validation/divmod_axioms_nia.smt2: cvc5 and z3 both return
 * unsat for every negated axiom, over the UNBOUNDED integers) and by
 * ESBMC over the uint64 domain (axiom_validation/validate_specs_axioms.c,
 * divmod_bounds()).
 *
 * Integer division and modulo are NONLINEAR, which WP's SMT back-ends
 * reason about only weakly (Alt-Ergo especially). These give the linear
 * consequences the range analysis needs. ACSL / and % truncate toward
 * zero; on the guarded domain (0 <= x, 1 <= y) truncated, floored and
 * Euclidean division all coincide, so the SMT-LIB (floor) validation is
 * faithful to the ACSL (truncating) reading.
 */
/*@
axiomatic DivModBounds {
	axiom div_nonneg:
		\forall integer x, y; 0 <= x && 1 <= y ==> 0 <= x / y;
	// Dividing a non-negative value by y >= 1 never grows it: carries
	// the else-branch usound upper bound (x/y <= x <= u.max) and every
	// uwidth chain (result <= dividend <= msk).
	axiom div_le:
		\forall integer x, y; 0 <= x && 1 <= y ==> x / y <= x;
	axiom mod_nonneg:
		\forall integer x, y; 0 <= x && 1 <= y ==> 0 <= x % y;
	// A remainder is strictly below its divisor: carries the else-branch
	// MOD bound u.max = RTE_MIN(u.max, rs.u.max - 1) via
	// x % y <= y - 1 <= rs.u.max - 1.
	axiom mod_lt_divisor:
		\forall integer x, y; 0 <= x && 1 <= y ==> x % y <= y - 1;
	// ...and never above the dividend (x % y == x when x < y, else
	// x % y < y <= x): carries the rd-side MOD bound and uwidth.
	axiom mod_le:
		\forall integer x, y; 0 <= x && 1 <= y ==> x % y <= x;
}
*/

#endif /* AXIOMS_DIV_H */
