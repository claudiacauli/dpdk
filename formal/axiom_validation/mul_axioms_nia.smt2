; Validation of the nonlinear-INTEGER MulBounds axioms (common/axioms_mul.h):
;   mul_nonneg, mul_mono, mul_bound_u32/u64/s32/s64.
; These are polynomial (in)equalities over Z, NOT bitwise — so they are
; validated with an NIA solver (cvc5/z3), which discharges them instantly
; over the UNBOUNDED integers (stronger than the uint64 instantiation domain).
; CBMC/ESBMC bit-blasting is the WRONG tool here: a 64-bit multiplier
; comparison (mul_mono) does not terminate in practice. The bitwise mul axiom
; (mul_mask_wrap, which has `& msk`) stays in validate_specs_axioms.c for
; ESBMC. Run:  cvc5 mul_axioms_nia.smt2   (and/or)  z3 mul_axioms_nia.smt2
; Every check must print  unsat  (the negated axiom is unsatisfiable => the
; axiom holds for all a,b,c,d).
(set-logic NIA)
(declare-const a Int)(declare-const b Int)(declare-const c Int)(declare-const d Int)
; mul_nonneg: 0<=a && 0<=b ==> 0 <= a*b
(push 1)(assert (and (<= 0 a)(<= 0 b)))(assert (not (<= 0 (* a b))))(check-sat)(pop 1)
; mul_mono: 0<=a<=c && 0<=b<=d ==> a*b <= c*d
(push 1)(assert (and (<= 0 a)(<= a c)(<= 0 b)(<= b d)))(assert (not (<= (* a b)(* c d))))(check-sat)(pop 1)
; mul_bound_u32: 0<=a,b<=2^16-1 ==> a*b <= 2^32-1
(push 1)(assert (and (<= 0 a)(<= a 65535)(<= 0 b)(<= b 65535)))(assert (not (<= (* a b) 4294967295)))(check-sat)(pop 1)
; mul_bound_u64: 0<=a,b<=2^32-1 ==> a*b <= 2^64-1
(push 1)(assert (and (<= 0 a)(<= a 4294967295)(<= 0 b)(<= b 4294967295)))(assert (not (<= (* a b) 18446744073709551615)))(check-sat)(pop 1)
; mul_bound_s32: 0<=a,b<=2^15-1 ==> a*b <= 2^31-1
(push 1)(assert (and (<= 0 a)(<= a 32767)(<= 0 b)(<= b 32767)))(assert (not (<= (* a b) 2147483647)))(check-sat)(pop 1)
; mul_bound_s64: 0<=a,b<=2^31-1 ==> a*b <= 2^63-1
(push 1)(assert (and (<= 0 a)(<= a 2147483647)(<= 0 b)(<= b 2147483647)))(assert (not (<= (* a b) 9223372036854775807)))(check-sat)(pop 1)
