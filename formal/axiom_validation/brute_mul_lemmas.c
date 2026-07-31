
#include <stdio.h>
#include <stdint.h>
static int W; static long long M, SMIN, SMAX;
static long long sext(long long p){ return p <= (M>>1) ? p : p - (M+1); }
int main(void){
	long bad_of = 0, bad_c = 0;
	for (W = 4; W <= 5; W++) {
		M = (1LL<<W)-1; SMAX = M>>1; SMIN = -SMAX-1;
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
		if (W == 4)
		for (a=SMIN;a<=SMAX;a++)for(c=SMIN;c<=SMAX;c++){
			long long X = sext((a*c)&M), Y = X;
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
