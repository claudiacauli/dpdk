#ifndef AXIOMS_DIV_H
#define AXIOMS_DIV_H

#include "../../common/specs.h"

/*@
axiomatic DivModBounds {
	axiom div_nonneg:
		\forall integer x, y; 0 <= x && 1 <= y ==> 0 <= x / y;
	axiom div_le:
		\forall integer x, y; 0 <= x && 1 <= y ==> x / y <= x;
	axiom mod_nonneg:
		\forall integer x, y; 0 <= x && 1 <= y ==> 0 <= x % y;
	axiom mod_lt_divisor:
		\forall integer x, y; 0 <= x && 1 <= y ==> x % y <= y - 1;
	axiom mod_le:
		\forall integer x, y; 0 <= x && 1 <= y ==> x % y <= x;
}
*/

#endif
