/* Exhaustive check of the mul_sext_congr congruence at widths 4/8/12:
 * the two's-complement argument is width-uniform, so any counterexample
 * class would appear here. Real masks (2^32-1, 2^64-1) proved
 * intractable for ESBMC on both machines (see the tier note on the
 * ESBMC cell in validate_specs_axioms.c) — this enumeration plus the
 * mod-2^w congruence argument is the axiom's validation evidence. */
#include <stdio.h>
#include <stdint.h>
int main(void) {
	for (int wbits = 4; wbits <= 12; wbits += 4) {
		long long m = (1LL << wbits) - 1, half = m >> 1;
		long long bad = 0;
		for (long long v = 0; v <= m; v++)
			for (long long w = 0; w <= m; w++) {
				long long c = (v <= half) ? v : v - (m + 1);
				long long e = (w <= half) ? w : w - (m + 1);
				long long pv = (v * w) & m;
				long long pc = (c * e) & m;
				long long dv = (pv <= half) ? pv : pv - (m + 1);
				long long dc = (pc <= half) ? pc : pc - (m + 1);
				if (dv != dc) bad++;
			}
		printf("w=%d: %lld violations of %lld cases\n", wbits, bad, (m+1)*(m+1));
	}
	return 0;
}
