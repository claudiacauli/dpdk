/* Exhaustive small-width validation of the two AXIOMS mul_ssound_overflow /
 * mul_ssound_const (harnesses/eval_mul/eval_mul.h) — the signed folded
 * soundness statements that WP does not prove under the intersection-form
 * bin_witness (red in the @lemma batch at 900s and isolated at 1800s,
 * alt-ergo/z3/cvc5, 2026-07-28). Checked in their WORST case:
 * od.u = os.u = [0,M] for _overflow (fullest gamma; a thinner u-track only
 * removes witnesses), and ALL u-range x s-constant combinations for _const
 * at w=4. The conclusion is checked against the TIGHTEST nw allowed by the
 * hypotheses (X,Y = the corner-product brackets), so any admissible looser
 * nw also passes. The congruence argument (witness == decode mod M+1, per
 * to_signed's single-period subtraction) is width-uniform, so a
 * counterexample class would appear at these widths — same validation tier
 * as mul_sext_congr (see brute_sext_congr.c and the ESBMC cells in
 * validate_specs_axioms.c).
 * Recorded run (cc -O2, 2026-07-28):
 *   W=4: overflow bad=0 const bad=0
 *   W=5: overflow bad=0 const bad=0
 *   ALL CLEAN                                  (0.07s user) */
#include <stdio.h>
#include <stdint.h>
static int W; static long long M, SMIN, SMAX;
static long long sext(long long p){ return p <= (M>>1) ? p : p - (M+1); }
int main(void){
	long bad_of = 0, bad_c = 0;
	for (W = 4; W <= 5; W++) {
		M = (1LL<<W)-1; SMAX = M>>1; SMIN = -SMAX-1;
		/* mul_ssound_overflow: 0<=smin<=smax both; Y=smaxd*smaxs<=M>>1 */
		long long a,b,c,d,x,y;
		for (a=0;a<=SMAX;a++)for(b=a;b<=SMAX;b++)
		for (c=0;c<=SMAX;c++)for(d=c;d<=SMAX;d++){
			long long X=a*c, Y=b*d;
			if (Y > (M>>1)) continue;
			for (x=0;x<=M;x++){ if(!(a<=sext(x)&&sext(x)<=b)) continue;
			for (y=0;y<=M;y++){ if(!(c<=sext(y)&&sext(y)<=d)) continue;
				long long p = sext((x*y)&M);
				if (p < X || p > Y) bad_of++;
			}}
		}
		/* mul_ssound_const: s consts, u ranges bound witnesses within width */
		if (W == 4)
		for (a=SMIN;a<=SMAX;a++)for(c=SMIN;c<=SMAX;c++){
			long long X = sext((a*c)&M), Y = X; /* both brackets same product */
			long long ulo1,uhi1,ulo2,uhi2;
			for(ulo1=0;ulo1<=M;ulo1++)for(uhi1=ulo1;uhi1<=M;uhi1++)
			for(ulo2=0;ulo2<=M;ulo2++)for(uhi2=ulo2;uhi2<=M;uhi2++)
			for (x=ulo1;x<=uhi1;x++){ if(sext(x)!=a) continue;
			for (y=ulo2;y<=uhi2;y++){ if(sext(y)!=c) continue;
				long long p = sext((x*y)&M);
				if (p < X || p > Y) bad_c++;
			}}
		}
		printf("W=%d: overflow bad=%ld const bad=%ld\n", W, bad_of, bad_c);
	}
	printf((bad_of||bad_c) ? "VIOLATIONS\n" : "ALL CLEAN\n");
	return (bad_of||bad_c)!=0;
}
