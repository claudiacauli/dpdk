; Validation of the nonlinear-INTEGER DivModBounds axioms
; (harnesses/eval_divmod/axioms_div.h):
;   div_nonneg, div_le, mod_nonneg, mod_lt_divisor, mod_le.
; These are div/mod (in)equalities over Z with NO bitwise operator, so they
; are validated with an NIA solver over the UNBOUNDED integers (stronger
; than the uint64 instantiation domain) — same method as
; mul_axioms_nia.smt2. SMT-LIB div/mod floor for a positive divisor; ACSL
; / and % truncate toward zero; on the guarded domain 0 <= x, 1 <= y the
; two coincide, so this reading is faithful.
; Run:  cvc5 --incremental divmod_axioms_nia.smt2   (and/or)
;       z3 divmod_axioms_nia.smt2
; Every check must print  unsat  (the negated axiom is unsatisfiable =>
; the axiom holds for all x, y).
(set-logic NIA)
(declare-const x Int)(declare-const y Int)
; div_nonneg: 0<=x && 1<=y ==> 0 <= x/y
(push 1)(assert (and (<= 0 x)(<= 1 y)))(assert (not (<= 0 (div x y))))(check-sat)(pop 1)
; div_le: 0<=x && 1<=y ==> x/y <= x
(push 1)(assert (and (<= 0 x)(<= 1 y)))(assert (not (<= (div x y) x)))(check-sat)(pop 1)
; mod_nonneg: 0<=x && 1<=y ==> 0 <= x%y
(push 1)(assert (and (<= 0 x)(<= 1 y)))(assert (not (<= 0 (mod x y))))(check-sat)(pop 1)
; mod_lt_divisor: 0<=x && 1<=y ==> x%y <= y-1
(push 1)(assert (and (<= 0 x)(<= 1 y)))(assert (not (<= (mod x y) (- y 1))))(check-sat)(pop 1)
; mod_le: 0<=x && 1<=y ==> x%y <= x
(push 1)(assert (and (<= 0 x)(<= 1 y)))(assert (not (<= (mod x y) x)))(check-sat)(pop 1)
