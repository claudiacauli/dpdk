#ifndef SEMANTICS_H
#define SEMANTICS_H

#include "axioms.h"

/*@
logic integer neg_pat(integer x, integer msk) =
	x == 0 ? 0 : msk + 1 - x;
*/

#define SEM_ADD(x, y, msk)	(((x) + (y)) & (msk))

#define SEM_SUB(x, y, msk)	(((x) - (y)) & (msk))

#define SEM_MUL(x, y, msk)	(((x) * (y)) & (msk))

#define SEM_NEG(x, msk)		neg_pat((x), (msk))

#define SEM_AND(x, y, msk)	((x) & (y))

#define SEM_OR(x, y, msk)	((x) | (y))

#define SEM_XOR(x, y, msk)	((x) ^ (y))

#define SEM_LSH(x, y, msk)	(((x) << (y)) & (msk))

#define SEM_RSH(x, y, msk)	((x) >> (y))

#define SEM_ARSH(v, y, msk)	(to_signed((v), (msk)) >> (y))

#define SEM_DIV(x, y)		((x) / (y))
#define SEM_MOD(x, y)		((x) % (y))

#define SEM_MASK(x, msk)	((x) & (msk))

#define SEM_FILL(imm, msk)	(((uint64_t)(imm)) & (msk))

#endif
