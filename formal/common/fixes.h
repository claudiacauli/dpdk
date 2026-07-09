#ifndef FIXES_H
#define FIXES_H

/* Master switch: -DALL_FIXES enables every registered fix. */
#ifdef ALL_FIXES
#  define FIX_APPLY_MASK_SIGNED
#  define FIX_ADD_SIGNED_32

#endif

#endif /* FIXES_H */
