#ifndef AXIOMS_ARSH_H
#define AXIOMS_ARSH_H

#include "shared.h"

/*
 * Trusted axioms used ONLY by the eval_arsh proof, deliberately kept
 * out of common/axioms.h: quantified axioms perturb the SMT search
 * of every PO in whose translation unit they appear, even when their
 * triggers cannot fire — adding these two identity axioms to the
 * shared header pushed eval_add's (unrelated) soundness goals from
 * proving in 8'55" to timing out at 3000s. Include from eval_arsh.h
 * only. Same trust contract as axioms.h: every axiom is CBMC-proved
 * in axiom_validation/validate_specs_axioms.c.
 */

// Arithmetic-shift support (eval_arsh): the LenShift axioms are all
// 0 <= x guarded, but ARSH shifts NEGATIVE canonical values, where
// ACSL's >> is floor division (exactly the machine's arithmetic
// shift). Value-monotonicity holds for all signs; amount-monotonicity
// FLIPS for negatives (a bigger shift moves the value up, toward -1);
// and asr_both_neg is the combined form triggering on the two terms
// the eval_arsh POs actually contain, (min >> min-shift) and
// (max >> max-shift) — mirroring lsl_both_mono / lsr_both_anti. All
// CBMC-checked over the full int64 domain
// (axiom_validation/validate_specs_axioms.c).
/*@
axiomatic ArshShift {
	axiom asr_val_mono:
		\forall integer a, b, y;
		a <= b && 0 <= y ==> (a >> y) <= (b >> y);
	axiom asr_amt_mono_neg:
		\forall integer x, p, q;
		x < 0 && 0 <= p <= q ==> (x >> p) <= (x >> q);
	axiom asr_neg_bounds:
		\forall integer x, y;
		x < 0 && 0 <= y ==> x <= (x >> y) <= -1;
	axiom asr_both_neg:
		\forall integer a, b, p, q;
		a <= b && b < 0 && 0 <= p <= q ==> (a >> p) <= (b >> q);
	// The FIX_ARSH_32EXT_SHL dance shifts the canonical int32 up by 32
	// in uint64: for negative v the PO term
	// to_sint64(to_uint64(lsl(to_uint64(v), 32))) can only collapse by
	// unfolding to_uint64's +/-2^64 recursion ~2^32 times — impossible
	// first-order, so the identity is supplied whole (int64_t binder so
	// the trigger matches the machine-term shape verbatim).
	axiom shl32_ext_id:
		\forall int64_t v;
		-0x80000000 <= v < 0x80000000 ==>
		(int64_t)(((uint64_t)v) << 32) == v * 0x100000000;
	// De-scaling: floor((v*2^32) / 2^w) == floor(v / 2^(w-32)); with
	// w == q+32 this turns the 32ext-shifted arithmetic shift back into
	// the bare v >> q the asr_* axioms reason about.
	axiom asr_descale32:
		\forall integer v, w;
		-0x80000000 <= v < 0x80000000 && 32 <= w <= 63 ==>
		((v * 0x100000000) >> w) == (v >> (w - 32));
}
*/


#endif /* AXIOMS_ARSH_H */
