#ifndef FIXES_H
#define FIXES_H

/* Master switch: -DALL_FIXES enables every registered fix. */
#ifdef ALL_FIXES
#  define FIX_APPLY_MASK_SIGNED
#  define FIX_ADD_SIGNED_32
#  define FIX_SUB_SIGNED_32
#  define FIX_ARSH_32EXT_SHL
#  define FIX_ARSH_SIGNED_MASK
#  define FIX_ARSH_UNSIGNED_SIGN
#  define FIX_UMAX_BITS_32
#  define FIX_AND_SIGNED_GUARD
#  define FIX_MUL_UGUARD
#  define FIX_MUL_SCONST
#  define FIX_MUL_SGUARD
#  define FIX_DIVMOD_SIGNED_32
#  define FIX_NEG_SIGNED_32
#  define FIX_FILL_IMM_SIGNED_32
#  define FIX_APPLY_MASK_CONSIST
#  define FIX_NEG_CROSS_INVERT  /* cross-track clamps can cross -> empty interval */

/* Precision / optimality fixes: correct upstream IMPRECISION (the computed
 * range is sound but looser than optimal). Unlike the soundness fixes above,
 * these are not needed for soundness — they make the range TIGHT so the
 * tightness/optimality contracts can hold. See formal/optimality_notes.md. */
#  define FIX_ADD_SIGNED_OVFL   /* spurious signed widening on negative-source add */
#  define FIX_SUB_SIGNED_OVFL   /* same family: spurious signed widening on negative-subtrahend sub */
#  define FIX_NEG_ZERO          /* include-0 unsigned max widened past -s.min */

/* Carry-parity overflow handling for eval_add/eval_sub: widen ONLY on a wrap
 * MISMATCH between the two corners (a straddling wrap), not on any wrap. The
 * kept uniform-wrap interval is exact, so the uopt/sopt guards weaken from
 * NO-overflow to UNIFORM-overflow (equal carries / equal trits) -- ~1.5x the
 * unsigned coverage. NOT unconditional: top's endpoints are interior points the
 * intersection gamma need not contain (brute-refuted; see eval_add.c notes).
 * _OPT macros supersede the corresponding FIX_*_SIGNED_OVFL. A FIX_NEG_OPT
 * (dropping neg's INT_MIN guard) was refuted by the same argument and
 * withdrawn -- see eval_neg.c. */
#  define FIX_ADD_UNSIGNED_OVFL   /* unsigned carry-parity + equal-carry uopt guard */
#  define FIX_ADD_SIGNED_OVFL_OPT /* signed trit-parity + equal-trit sopt guard */
#  define FIX_SUB_UNSIGNED_OVFL   /* sub borrow-parity twin */
#  define FIX_SUB_SIGNED_OVFL_OPT /* sub signed twin */
#  define FIX_APPLY_MASK_OPT      /* unsigned masking: widen on block-straddle only; uopt unconditional */

#endif

#endif /* FIXES_H */
