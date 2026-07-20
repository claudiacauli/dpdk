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

#endif

#endif /* FIXES_H */
