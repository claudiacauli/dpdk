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

#endif

#endif /* FIXES_H */
