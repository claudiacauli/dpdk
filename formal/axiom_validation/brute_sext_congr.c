
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
