#ifndef SEMANTICS_H
#define SEMANTICS_H

#include "axioms.h"	/* to_signed, op_bits */

/*
 * THE CONCRETE PER-INSTRUCTION SEMANTICS — single source of truth.
 *
 * ⟦op⟧ for each BPF ALU instruction, at width w via msk = 2^w - 1, on
 * operands already within width. Two families of theorems cite these
 * and ONLY these:
 *
 *   - the VALIDATOR side (harnesses/eval_*): every soundness/optimality
 *     predicate's image term is a SEM_* application — "the abstract
 *     transformer brackets/attains SEM_op over the witnesses";
 *   - the EXECUTOR side (harnesses/exec_*): every per-opcode agreement
 *     ensures is a SEM_* application — "the interpreter case-arm in
 *     lib/bpf/bpf_exec.c computes exactly SEM_op".
 *
 * With both sides referencing one definition, "does the abstraction
 * model the runtime?" stops being a sync discipline and becomes a
 * by-construction property: there is nothing to drift. The residual
 * sync surface is harness-body-vs-upstream fidelity only.
 *
 * WHY CPP MACROS AND NOT ACSL LOGIC FUNCTIONS. Annotations are
 * preprocessed (the corpus already relies on this: _32_BIT_MASK,
 * INT32_MIN etc. appear in contracts), so a macro expands inside ACSL
 * to the IDENTICAL AST the predicates contained before the refactor —
 * proof replay is by construction, no term-shape change, no trigger
 * churn. A logic function would put an L_sem_* node into every goal and
 * break the corpus's tuned axiom trigger shapes (documented cliff
 * sensitivity). MEASURED: the eval_add refactor replayed green with
 * identical goal counts (2026-07-28).
 *
 * The two piecewise helpers BELOW are genuine logic functions, not
 * macros, because that is what they already were — they moved here
 * verbatim from eval_sub.h / eval_neg.h so that the executor harnesses
 * can cite the same symbol the validator predicates do. Moving a
 * defined logic function does not change any goal.
 *
 * OPERAND-WIDTH CONVENTION. SEM_* operands are mathematical integers
 * expected within [0, msk] (the validator quantifies witnesses under
 * that invariant). Executor registers are arbitrary uint64, and the
 * case-arm casts truncate them, so the exec theorems apply SEM_* to
 * (operand & msk) — exactly the masking eval_alu models with
 * eval_apply_mask (eval_alu.c:143-164). Shift COUNTS are NOT masked by
 * the executor (see the UB note at SEM_LSH) — state the count as the
 * masked source only where the case-arm's cast does the masking.
 *
 * GROWTH RULE. Copy each SEM_* body CHAR-FOR-CHAR from the operator's
 * predicate image term (modulo argument parentheses, which do not
 * change the AST). Where the signed image is NOT to_signed(SEM, msk),
 * that is documented per operator below.
 */

/*@
// Machine result of a w-bit subtraction, for differences within one wrap
// (|d| <= msk, guaranteed by the operand ranges): piecewise-linear on
// purpose — a negative d under ACSL's `&` has no usable axioms, while
// this form needs none (same strategy as to_signed for eval_add).
// MOVED here from eval_sub.h (2026-07-28) so exec_* can cite it.
logic integer wrap_diff(integer d, integer msk) =
      d >= 0 ? d : d + (msk + 1);

// Machine result of a w-bit negation. MOVED here from eval_neg.h.
// neg_pat maps [0,msk] onto itself and is an INVOLUTION there — that is
// what makes op-optimality provable for eval_neg at all.
//
// DELIBERATELY NOT ACCOMPANIED BY LEMMAS -- do not add them. Quantified
// lemmas of the form
//     \forall x, m; 0 <= x <= m ==> neg_pat(neg_pat(x, m), m) == x
// were tried and MEASURED: they take eval_neg's usound from 1/1 in 4.8s
// to a TIMEOUT at 5m07s, because usound itself quantifies over neg_pat
// so the trigger fires all over its proof obligation. They are also
// unnecessary: neg_pat is a DEFINED logic function, so WP unfolds it,
// and the four GROUND instances stated as stones in eval_neg.c each
// prove 1/1. General rule: when a fact is needed only at specific
// terms, state it as a GROUND STONE, not a quantified lemma.
logic integer neg_pat(integer x, integer msk) =
	x == 0 ? 0 : msk + 1 - x;
*/

/* ---- wrapping arithmetic: signed image is to_signed(SEM, msk) ------- */

/* ⟦add⟧ — bpf_exec.c:174/208/253/290 (K/X x 32/64). */
#define SEM_ADD(x, y, msk)	(((x) + (y)) & (msk))

/* ⟦sub⟧ — bpf_exec.c:177/211/256/293. Helper form, not `&`: see wrap_diff. */
#define SEM_SUB(x, y, msk)	wrap_diff((x) - (y), (msk))

/* ⟦mul⟧ — bpf_exec.c:195/229/277/314. */
#define SEM_MUL(x, y, msk)	(((x) * (y)) & (msk))

/* ⟦neg⟧ — bpf_exec.c:243/328. The case-arm negates the UNCAST uint64 then
 * truncates; congruent to negate-after-truncate, which is this form. */
#define SEM_NEG(x, msk)		neg_pat((x), (msk))

/* ---- bitwise: no outer mask (operands already within width) --------- */

/* ⟦and⟧ — bpf_exec.c:180/213/259/295. msk unused: eval_and's image term
 * carries no outer mask (and-of-in-range is in range). Kept in the
 * signature for uniformity across the family. */
#define SEM_AND(x, y, msk)	((x) & (y))

/* ⟦or⟧ — bpf_exec.c:183/216/262/298. NOTE: eval_or's ssound image wraps
 * an extra `& msk` inside to_signed while uopt/sopt do not (pre-existing
 * AST debt, harmless: equal for in-range operands). */
#define SEM_OR(x, y, msk)	((x) | (y))

/* ⟦xor⟧ — bpf_exec.c:192/225/273/310. Same ssound/sopt note as SEM_OR. */
#define SEM_XOR(x, y, msk)	((x) ^ (y))

/* ---- shifts: the executor does NOT mask the count ------------------- */

/*
 * SHIFT-COUNT UB (BACKLOG E7/E8). The executor applies C <</>> with an
 * unmasked runtime count, so count >= width is UNDEFINED in the shipped
 * interpreter, and the x86 JIT additionally MIS-ENCODES immediate counts
 * outside [-128,127] (E8: stray bytes, memory corruption). The validator
 * neither rejects such programs nor models them — it widens to Top. The
 * exec agreement theorems are therefore preconditioned on in-range
 * counts, and the residue is an upstream defect, not a provable
 * agreement. The validator's own soundness predicates likewise quantify
 * y < op_bits(msk).
 */

/* ⟦lsh⟧ — bpf_exec.c:186/220/265/302. */
#define SEM_LSH(x, y, msk)	(((x) << (y)) & (msk))

/* ⟦rsh⟧ (logical) — bpf_exec.c:189/223/268/305. No outer mask: eval_rsh's
 * image term has none (shifting an in-range value right stays in range). */
#define SEM_RSH(x, y, msk)	((x) >> (y))

/*
 * ⟦arsh⟧ (arithmetic) — bpf_exec.c:271/308, ALU64 ONLY (32-bit ARSH has
 * no case arm and no ins_chk row: rejected at load on both sides).
 * THE ONLY OPERATOR WHOSE SIGNED IMAGE IS PRIMARY: this macro IS
 * eval_arsh's signed image term (no to_signed wrapper, no outer mask),
 * and the UNSIGNED image is derived from it by re-encoding:
 *     (((uint64_t)SEM_ARSH(x, y, msk)) & msk)
 * ACSL's >> on mathematical integers is floor division by 2^y, which is
 * exactly the sign-replicating machine shift on the canonical value.
 */
#define SEM_ARSH(v, y, msk)	(to_signed((v), (msk)) >> (y))

/* ---- division: unsigned; zero divisor never yields a value ---------- */

/*
 * ⟦div⟧/⟦mod⟧ — bpf_exec.c:198/233/280/318 and :201/237/283/322.
 * Unsigned throughout (no SDIV/SMOD opcode exists), so no INT_MIN/-1
 * trap. Zero divisor: the X case-arms run BPF_DIV_ZERO_CHECK
 * (bpf_exec.c:46-54) which ABORTS THE WHOLE PROGRAM (returns 0) before
 * computing, so agreement is stated only on the divisor-nonzero path —
 * matching eval_divmod's `1 <= y` witness guard. The K case-arms have NO
 * runtime check and rely entirely on ins_chk's `.imm.min = 1`
 * (bpf_validate.c:1723-1734, :1796-1807).
 */
#define SEM_DIV(x, y)		((x) / (y))
#define SEM_MOD(x, y)		((x) % (y))

/* ---- value materialisation ----------------------------------------- */

/* ⟦mask⟧ — the width truncation eval_apply_mask models; also MOV-X. */
#define SEM_MASK(x, msk)	((x) & (msk))

/*
 * ⟦fill⟧ — an int32 immediate materialised at width w: cast to uint64
 * (SIGN-extension, since imm is int32_t) then masked. This is
 * eval_fill_imm's `((uint64_t)imm) & mask` verbatim, and it matches the
 * executor's `(uint64_t)ins->imm` at 64-bit and `(uint32_t)ins->imm` at
 * 32-bit (mask-after-sign-extend == direct truncation at 32 bits).
 * The 32-vs-64 asymmetry that FIX_FILL_IMM_SIGNED_32 concerns is in the
 * SIGNED TRACK's encoding, not in this value.
 */
#define SEM_FILL(imm, msk)	(((uint64_t)(imm)) & (msk))

#endif /* SEMANTICS_H */
