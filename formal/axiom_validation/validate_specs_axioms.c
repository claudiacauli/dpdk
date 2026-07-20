/*
 * CBMC validation of every trusted axiom in common/specs.h.
 *
 *     cbmc validate_specs_axioms.c
 *
 * must print VERIFICATION SUCCESSFUL. Re-run whenever an axiom is added
 * or changed; an axiom that is false makes every WP proof worthless.
 *
 * Domain convention (matches how the axioms are instantiated in the WP
 * proof obligations): WP's unbounded mathematical integers are modelled
 * with uint64_t / int64_t values and shift amounts in [0, 64]; shift
 * products are computed in unsigned __int128 (holds up to 2^128 - 1;
 * the largest product reached is (2^64-1) << 63 < 2^127). Values that
 * only arise above 2^64 (the land_wrap hypotheses) are modelled directly
 * in unsigned __int128.
 */
#include <stdint.h>
#include <assert.h>

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
unsigned __int128 nondet_u128(void);

#define ALL1 0xFFFFFFFFFFFFFFFFULL

/* ---------------- LandMaskBound / LandBounds / all-ones ids ------------ */

static void land_family(void)
{
	/* land_le_mask: 0<=x, 0<=y ==> 0 <= (x & y) <= y */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		assert((x & y) <= y);
	}
	/* land_nonneg_le: 0<=x, 0<=y ==> 0 <= (x & y) <= x */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		assert((x & y) <= x);
	}
	/* land_id_u64 / land_uint64_max: 0<=x<=2^64-1 ==> (x & 2^64-1) == x */
	{
		uint64_t x = nondet_u64();
		assert((x & ALL1) == x);
	}
	/* land_id_u32 / land_uint32_max: 0<=x<=2^32-1 ==> (x & 2^32-1) == x */
	{
		uint64_t x = nondet_u64();
		if (x <= 0xFFFFFFFFULL)
			assert((x & 0xFFFFFFFFULL) == x);
	}
}

/* ---------------- LandWrap / LandWrapTop ------------------------------- */

static void land_wrap_family(void)
{
	/* land_wrap_u32: 2^32-1 < x <= 2*(2^32-1) ==>
	   (x & 0xFFFFFFFF) == x - 0x100000000 */
	{
		uint64_t x = nondet_u64();
		if (0xFFFFFFFFULL < x && x <= 2 * 0xFFFFFFFFULL)
			assert((x & 0xFFFFFFFFULL) == x - 0x100000000ULL);
	}
	/* land_wrap_u64: 2^64-1 < x <= 2*(2^64-1) ==>
	   (x & (2^64-1)) == x - 2^64  (x lives above uint64: use __int128) */
	{
		unsigned __int128 x = nondet_u128();
		if ((unsigned __int128)ALL1 < x &&
		    x <= (unsigned __int128)2 * ALL1)
			assert((x & (unsigned __int128)ALL1) ==
			       x - ((unsigned __int128)1 << 64));
	}
	/* land_wrap_u32_top: 2^64-2^32 <= x <= 2^64-1 ==>
	   (x & 0xFFFFFFFF) == x - 0xFFFFFFFF00000000 */
	{
		uint64_t x = nondet_u64();
		if (x >= 0xFFFFFFFF00000000ULL)
			assert((x & 0xFFFFFFFFULL) ==
			       x - 0xFFFFFFFF00000000ULL);
	}
}

/* ---------------- BpfArgPtrType ---------------------------------------- */

static void bpf_arg_ptr_type(void)
{
	/* ptr_flag_excludes_scalars: (t & 0x10) != 0 ==> t != 0 && t != 1
	   no_ptr_flag_excludes_pointers: (t & 0x10) == 0 ==>
	       t != 0x10 && t != 0x11 && t != 0x12 */
	int64_t t = nondet_i64();
	if ((t & 0x10) != 0)
		assert(t != 0 && t != 1);
	else
		assert(t != 0x10 && t != 0x11 && t != 0x12);
}

/* ---------------- LenShift: unsigned core ------------------------------ */

static void lenshift_core(void)
{
	/* lsl_nonneg: 0<=x, 0<=y ==> 0 <= (x << y) — trivial in the
	   unsigned model; recorded for completeness. */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (y <= 64) {
			unsigned __int128 p = (unsigned __int128)x << y;
			assert(p >= 0);
		}
	}
	/* lsl_val_mono: 0<=a<=b, 0<=y ==> (a<<y) <= (b<<y) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), y = nondet_u64();
		if (a <= b && y <= 64)
			assert(((unsigned __int128)a << y) <=
			       ((unsigned __int128)b << y));
	}
	/* lsl_amt_mono: 0<=x, 0<=p<=q ==> (x<<p) <= (x<<q) */
	{
		uint64_t x = nondet_u64(), p = nondet_u64(), q = nondet_u64();
		if (p <= q && q <= 64)
			assert(((unsigned __int128)x << p) <=
			       ((unsigned __int128)x << q));
	}
	/* lsl_both_mono: 0<=a<=b, 0<=p<=q ==> (a<<p) <= (b<<q) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && p <= q && q <= 64)
			assert(((unsigned __int128)a << p) <=
			       ((unsigned __int128)b << q));
	}
	/* lsl_width_bound: 0<=k<=w, 0<=x<=2^(w-k)-1 ==> (x<<k) <= 2^w - 1 */
	{
		uint64_t x = nondet_u64(), k = nondet_u64(), w = nondet_u64();
		if (k <= w && w <= 64 &&
		    x <= (((unsigned __int128)1 << (w - k)) - 1))
			assert(((unsigned __int128)x << k) <=
			       ((unsigned __int128)1 << w) - 1);
	}
	/* lsr_shrink: 0<=x, 0<=y ==> 0 <= (x >> y) <= x */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (y <= 64)
			assert((y == 64 ? 0 : x >> y) <= x);
	}
	/* lsr_val_mono: 0<=a<=b, 0<=y ==> (a>>y) <= (b>>y) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), y = nondet_u64();
		if (a <= b && y <= 63)
			assert((a >> y) <= (b >> y));
	}
	/* lsr_amt_anti: 0<=x, 0<=p<=q ==> (x>>q) <= (x>>p) */
	{
		uint64_t x = nondet_u64(), p = nondet_u64(), q = nondet_u64();
		if (p <= q && q <= 63)
			assert((x >> q) <= (x >> p));
	}
	/* lsr_both_anti: 0<=a<=b, 0<=p<=q ==> (a>>q) <= (b>>p) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && p <= q && q <= 63)
			assert((a >> q) <= (b >> p));
	}
}

/* ---------------- LenShift: mask-concrete width bounds ----------------- */

static void lenshift_width(void)
{
	/* lsl_width_32: 0<=k<32, 0<=x<=(2^64-1)>>(64-(32-k)) ==>
	   (x<<k) <= 0xFFFFFFFF */
	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k < 32 && x <= (ALL1 >> (unsigned)(64 - (32 - k))))
			assert(((unsigned __int128)x << k) <= 0xFFFFFFFFULL);
	}
	/* lsl_width_64: 0<=k<64, 0<=x<=(2^64-1)>>(64-(64-k)) ==>
	   (x<<k) <= 2^64-1 */
	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k < 64 && k >= 1 && x <= (ALL1 >> (unsigned)k))
			assert(((unsigned __int128)x << k) <= ALL1);
		if (k == 0)
			assert(((unsigned __int128)x << k) <= ALL1);
	}
}

/* ---------------- LenShift: signed-branch support ----------------------- */

static void lenshift_signed(void)
{
	/* lsr_sign_any: int64 v, 31<=w<=63, ((uint64_t)v >> w) == 0 ==>
	   0 <= v  ((uint64_t)v is exactly WP's to_uint64(v)) */
	{
		int64_t v = nondet_i64();
		uint64_t w = nondet_u64();
		if (31 <= w && w <= 63 && (((uint64_t)v >> w) == 0))
			assert(0 <= v);
	}
	/* lsr_allones_sint: 1<=k<=63 ==> 0 <= (2^64-1)>>k <= 2^63-1 */
	{
		uint64_t k = nondet_u64();
		if (1 <= k && k <= 63)
			assert((ALL1 >> k) <= 0x7FFFFFFFFFFFFFFFULL);
	}
	/* lsr_allones_33: 33<=k<=63 ==> (2^64-1)>>k <= 2^31-1 */
	{
		uint64_t k = nondet_u64();
		if (33 <= k && k <= 63)
			assert((ALL1 >> k) <= 0x7FFFFFFFULL);
	}
	/* lsl_swidth_32: 0<=k<=30, 0<=x, x < (2^64-1)>>(64-(32-k-1)) ==>
	   (x<<k) <= 0x7FFFFFFF */
	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k <= 30 &&
		    x < (ALL1 >> (unsigned)(64 - (32 - k - 1))))
			assert(((unsigned __int128)x << k) <= 0x7FFFFFFFULL);
	}
	/* lsl_swidth_64: 0<=k<=62, 0<=x, x < (2^64-1)>>(64-(64-k-1)) ==>
	   (x<<k) <= 2^63-1 */
	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k <= 62 &&
		    x < (ALL1 >> (unsigned)(64 - (64 - k - 1))))
			assert(((unsigned __int128)x << k) <=
			       0x7FFFFFFFFFFFFFFFULL);
	}
}

/* ---------------- ArshShift: negative-operand arithmetic shifts -------- */

static void arshshift(void)
{
	/* asr_val_mono: a <= b && 0 <= y ==> (a>>y) <= (b>>y), all signs */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		uint64_t y = nondet_u64();
		if (a <= b && y <= 63)
			assert((a >> y) <= (b >> y));
	}
	/* asr_amt_mono_neg: x < 0 && 0 <= p <= q ==> (x>>p) <= (x>>q) */
	{
		int64_t x = nondet_i64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (x < 0 && p <= q && q <= 63)
			assert((x >> p) <= (x >> q));
	}
	/* asr_neg_bounds: x < 0 && 0 <= y ==> x <= (x>>y) <= -1 */
	{
		int64_t x = nondet_i64();
		uint64_t y = nondet_u64();
		if (x < 0 && y <= 63)
			assert(x <= (x >> y) && (x >> y) <= -1);
	}
	/* asr_both_neg: a <= b < 0 && 0 <= p <= q ==> (a>>p) <= (b>>q) */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && b < 0 && p <= q && q <= 63)
			assert((a >> p) <= (b >> q));
	}
	/* shl32_ext_id: canonical int32 v ==>
	   (int64_t)((uint64_t)v << 32) == v * 2^32 */
	{
		int64_t v = nondet_i64();
		if (-0x80000000LL <= v && v < 0x80000000LL)
			assert((int64_t)((uint64_t)v << 32) ==
			       v * 0x100000000LL);
	}
	/* asr_descale32: canonical int32 v, 32 <= w <= 63 ==>
	   (v * 2^32) >> w == v >> (w - 32) */
	{
		int64_t v = nondet_i64();
		uint64_t w = nondet_u64();
		if (-0x80000000LL <= v && v < 0x80000000LL &&
		    32 <= w && w <= 63) {
			__int128 p = (__int128)v * 0x100000000LL;
			assert((int64_t)(p >> w) == (v >> (w - 32)));
		}
	}
}

/* ---------------- ClzWindow (common/axioms_clz.h) ----------------------- */

static void clz_window(void)
{
	/* clz_window_hi: (v >> (63-r)) == 1 ==> v <= allones >> r */
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1)
			assert(v <= (ALL1 >> r));
	}
	/* clz_window_lo: (v >> (63-r)) == 1 ==> ((allones >> r) >> 1) < v */
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1)
			assert(((ALL1 >> r) >> 1) < v);
	}
	/* allones_shr_shape: (allones >> r) is 2^k - 1 */
	{
		uint64_t r = nondet_u64();
		if (r <= 63)
			assert(((ALL1 >> r) & ((ALL1 >> r) + 1)) == 0);
	}
	/* clz_mask_width_32: window && v <= 2^32-1 ==> allones >> r <= 2^32-1 */
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 && v <= 0xFFFFFFFFULL)
			assert((ALL1 >> r) <= 0xFFFFFFFFULL);
	}
	/* clz_mask_half32: window && v <= 2^31-1 ==> allones >> r <= 2^31-1 */
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 && v <= 0x7FFFFFFFULL)
			assert((ALL1 >> r) <= 0x7FFFFFFFULL);
	}
	/* clz_mask_half64: window && v <= 2^63-1 ==> allones >> r <= 2^63-1 */
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 &&
		    v <= 0x7FFFFFFFFFFFFFFFULL)
			assert((ALL1 >> r) <= 0x7FFFFFFFFFFFFFFFULL);
	}
}

/* ---------------- LandCanon (common/axioms_and.h) ----------------------- */

static void land_canon(void)
{
	/* land_canon_32: canonical int32 a, b ==> a & b canonical int32 */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a & b) &&
			       (a & b) <= 0x7FFFFFFFLL);
	}
	/* land_canon_64: canonical int64 a, b ==> a & b canonical int64
	   (math &: compute sign-extended in __int128) */
	{
		__int128 a = nondet_i64(), b = nondet_i64();
		__int128 r = a & b;
		assert(-((__int128)1 << 63) <= r &&
		       r <= ((__int128)1 << 63) - 1);
	}
	/* land_allones_mono: 0<=a<=m1, 0<=b<=m2, m1/m2 all-ones ==>
	   (a & b) <= (m1 & m2) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t m1 = nondet_u64(), m2 = nondet_u64();
		if (a <= m1 && b <= m2 &&
		    (m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0)
			assert((a & b) <= (m1 & m2));
	}
	/* land_allones_id: 0<=x<=m, m all-ones ==> (x & m) == x */
	{
		uint64_t x = nondet_u64(), m = nondet_u64();
		if (x <= m && (m & (m + 1)) == 0)
			assert((x & m) == x);
	}
	/* land_nonneg_any: ANY a (incl. negative), b >= 0 ==>
	   0 <= (a & b) <= b (math & via sign-extended __int128) */
	{
		__int128 a = nondet_i64();
		uint64_t b = nondet_u64();
		__int128 r = a & (__int128)b;
		assert(0 <= r && r <= (__int128)b);
	}
	/* land_half32_id / land_half64_id: concrete half-mask identities */
	{
		uint64_t x = nondet_u64();
		if (x <= 0x7FFFFFFFULL)
			assert((x & 0x7FFFFFFFULL) == x);
	}
	{
		uint64_t x = nondet_u64();
		if (x <= 0x7FFFFFFFFFFFFFFFULL)
			assert((x & 0x7FFFFFFFFFFFFFFFULL) == x);
	}
	/* land_allones_absorb: 0<=a<=m, m all-ones, 0<=b ==> (a & b) <= m */
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), m = nondet_u64();
		if (a <= m && (m & (m + 1)) == 0)
			assert((a & b) <= m);
	}
	/* to_signed_land_id_32: canonical int32 u ==>
	   to_signed(u & 0xFFFFFFFF, 0xFFFFFFFF) == u */
	{
		int64_t u = nondet_i64();
		if (-0x80000000LL <= u && u <= 0x7FFFFFFFLL) {
			__int128 p = (__int128)u & 0xFFFFFFFFULL;
			int64_t dec = (p <= 0x7FFFFFFFLL)
				? (int64_t)p
				: (int64_t)(p - 0x100000000LL);
			assert(dec == u);
		}
	}
	/* to_signed_land_id_64: canonical int64 u ==>
	   to_signed(u & (2^64-1), 2^64-1) == u */
	{
		int64_t u = nondet_i64();
		__int128 p = (__int128)u & (__int128)0xFFFFFFFFFFFFFFFFULL;
		__int128 half = (__int128)0x7FFFFFFFFFFFFFFFULL;
		__int128 dec = (p <= half) ? p : p - ((__int128)1 << 64);
		assert(dec == (__int128)u);
	}
	/* to_signed_land_pat: canonical v, pattern p <= m ==>
	   to_signed(v & p, m) == v & to_signed(p, m), both masks */
	{
		int64_t v = nondet_i64();
		uint64_t p64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64;
		if (-half - 1 <= v && v <= half && p <= m) {
			__int128 land_vp = (__int128)v & p;
			__int128 lhs = (land_vp <= half) ? land_vp
							 : land_vp - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			assert(lhs == ((__int128)v & dec_p));
		}
	}
}

/* ---------------- LorBounds (common/axioms_or.h) ----------------------- */

static void lor_bounds(void)
{
	/* lor_nonneg: 0<=a, 0<=b ==> 0 <= (a | b) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a | b) >= 0);
	}
	/* lor_lb: 0<=a, 0<=b ==> a <= (a | b) && b <= (a | b) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert(a <= (a | b) && b <= (a | b));
	}
	/* lor_id0: 0<=a ==> (a | 0) == a && (0 | a) == a */
	{
		uint64_t a = nondet_u64();
		assert((a | 0) == a && (0 | a) == a);
	}
	/* lor_canon_32: canonical int32 a, b ==> a | b canonical int32 */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a | b) &&
			       (a | b) <= 0x7FFFFFFFLL);
	}
	/* lor_canon_64: canonical int64 a, b ==> a | b canonical int64
	   (trivial in int64, but stated for parity) */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		int64_t r = a | b;
		assert(INT64_MIN <= r && r <= INT64_MAX);
	}
	/* lor_land_distrib: ((a | (b & m)) & m) == ((a | b) & m) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), m = nondet_u64();
		assert(((a | (b & m)) & m) == ((a | b) & m));
	}
	/* to_signed_lor_pat: canonical v, pattern p <= m ==>
	   to_signed((v | p) & m, m) == v | to_signed(p, m), both masks */
	{
		int64_t v = nondet_i64();
		uint64_t p64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64;
		if (-half - 1 <= v && v <= half && p <= m) {
			__int128 lor_vp = ((__int128)v | p) & m;
			__int128 lhs = (lor_vp <= half) ? lor_vp
							: lor_vp - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			assert(lhs == ((__int128)v | dec_p));
		}
	}
	/* to_signed_lor_both: patterns p, q <= m ==>
	   to_signed((p | q) & m, m) == to_signed(p, m) | to_signed(q, m),
	   both masks */
	{
		uint64_t p64 = nondet_u64(), q64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64, q = q64;
		if (p <= m && q <= m) {
			__int128 lor_pq = (p | q) & m;
			__int128 lhs = (lor_pq <= half) ? lor_pq
							: lor_pq - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			__int128 dec_q = (q <= half) ? q : q - (m + 1);
			assert(lhs == (dec_p | dec_q));
		}
	}
	/* lor_allones_mono: 0<=a<=m1, 0<=b<=m2, m1/m2 all-ones ==>
	   (a | b) <= (m1 | m2) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t m1 = nondet_u64(), m2 = nondet_u64();
		if (a <= m1 && b <= m2 &&
		    (m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0)
			assert((a | b) <= (m1 | m2));
	}
	/* lor_mask32: 0<=a<=2^32-1, 0<=b<=2^32-1 ==> (a | b) <= 2^32-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0xFFFFFFFFULL && b <= 0xFFFFFFFFULL)
			assert((a | b) <= 0xFFFFFFFFULL);
	}
	/* lor_mask64: 0<=a<=2^64-1, 0<=b<=2^64-1 ==> (a | b) <= 2^64-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a | b) <= ALL1);
	}
	/* lor_half32: 0<=a<=2^31-1, 0<=b<=2^31-1 ==> (a | b) <= 2^31-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0x7FFFFFFFULL && b <= 0x7FFFFFFFULL)
			assert((a | b) <= 0x7FFFFFFFULL);
	}
	/* lor_half64: 0<=a<=2^63-1, 0<=b<=2^63-1 ==> (a | b) <= 2^63-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0x7FFFFFFFFFFFFFFFULL && b <= 0x7FFFFFFFFFFFFFFFULL)
			assert((a | b) <= 0x7FFFFFFFFFFFFFFFULL);
	}
}

/* ---------------- LxorBounds (common/axioms_xor.h) --------------------- */

static void lxor_bounds(void)
{
	/* lxor_nonneg: 0<=a, 0<=b ==> 0 <= (a ^ b) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) >= 0);
	}
	/* lxor_le_lor: 0<=a, 0<=b ==> (a ^ b) <= (a | b) */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) <= (a | b));
	}
	/* lxor_mask32: 0<=a<=2^32-1, 0<=b<=2^32-1 ==> (a ^ b) <= 2^32-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0xFFFFFFFFULL && b <= 0xFFFFFFFFULL)
			assert((a ^ b) <= 0xFFFFFFFFULL);
	}
	/* lxor_mask64: 0<=a<=2^64-1, 0<=b<=2^64-1 ==> (a ^ b) <= 2^64-1 */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) <= ALL1);
	}
	/* lxor_canon_32: canonical int32 a, b ==> a ^ b canonical int32 */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a ^ b) &&
			       (a ^ b) <= 0x7FFFFFFFLL);
	}
	/* lxor_canon_64: canonical int64 a, b ==> a ^ b canonical int64
	   (trivial in int64, but stated for parity) */
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		int64_t r = a ^ b;
		assert(INT64_MIN <= r && r <= INT64_MAX);
	}
	/* to_signed_lxor_pat: canonical v, pattern p <= m ==>
	   to_signed((v ^ p) & m, m) == v ^ to_signed(p, m), both masks */
	{
		int64_t v = nondet_i64();
		uint64_t p64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64;
		if (-half - 1 <= v && v <= half && p <= m) {
			__int128 lxor_vp = ((__int128)v ^ p) & m;
			__int128 lhs = (lxor_vp <= half) ? lxor_vp
							 : lxor_vp - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			assert(lhs == ((__int128)v ^ dec_p));
		}
	}
	/* to_signed_lxor_both: patterns p, q <= m ==>
	   to_signed((p ^ q) & m, m) == to_signed(p, m) ^ to_signed(q, m),
	   both masks */
	{
		uint64_t p64 = nondet_u64(), q64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64, q = q64;
		if (p <= m && q <= m) {
			__int128 lxor_pq = (p ^ q) & m;
			__int128 lhs = (lxor_pq <= half) ? lxor_pq
							 : lxor_pq - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			__int128 dec_q = (q <= half) ? q : q - (m + 1);
			assert(lhs == (dec_p ^ dec_q));
		}
	}
}

/* ---------------- MulBounds (common/axioms_mul.h) --------------------- */

static void mul_bounds(void)
{
	/* mul_nonneg, mul_mono, mul_bound_u32/u64/s32/s64 are nonlinear-INTEGER
	   (in)equalities with NO bitwise operator, so they are validated with an
	   NIA solver in mul_axioms_nia.smt2 (cvc5 / z3 both return unsat over the
	   UNBOUNDED integers) — the correct tool. Bit-blasting them here is the
	   wrong tool: mul_mono's 64x64 multiplier comparison does not terminate
	   in CBMC/ESBMC in practice. Only the bitwise mul axiom (mul_mask_wrap,
	   below) stays in this SAT/SMT-bitvector harness. */
	/* mul_mask_wrap: low w bits of a product are wrap-invariant, so the
	   uint64-computed masked product (both constants branches,
	   `(uint64_t)((uint64_t)a*(uint64_t)b) & msk`) equals the mathematical
	   masked product (the soundness predicates, `(a*b) & msk`). a,b range
	   over ALL 2^64 residues (nondet_u64 covers every integer instance,
	   since the fact depends only on a,b mod 2^64); math product held in
	   unsigned __int128. The 64-bit multiplier makes this intractable for
	   CBMC's SAT bit-blasting (does not terminate in practice) — ESBMC's
	   SMT bit-vector backend discharges it in ~2s, so validate this file
	   with ESBMC. */
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		unsigned __int128 m = (unsigned __int128)ms[k];
		/* uint-product form (what both C constants branches compute) */
		uint64_t wrapped = a * b;                       /* uint64 2^64 wrap */
		unsigned __int128 lhs = (unsigned __int128)(wrapped & (uint64_t)m);
		/* math-product form (what the soundness predicates mask) */
		unsigned __int128 prod = (unsigned __int128)a * b;
		unsigned __int128 rhs = prod & m;
		assert(lhs == rhs);
	}
}

/* ---------------- DivModBounds (harnesses/eval_divmod/axioms_div.h) ---- */

static void divmod_bounds(void)
{
	/* The same facts are proved over the UNBOUNDED integers by NIA in
	   divmod_axioms_nia.smt2; this re-checks them bit-exactly on the
	   uint64 instantiation domain (single 64-bit udiv/urem — cheap for
	   ESBMC's SMT backend, unlike the eval_mul multipliers). */
	/* div_nonneg + div_le: 1<=y ==> 0 <= x/y <= x (nonneg is implicit
	   in the unsigned type; the assert carries the upper bound) */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (1 <= y)
			assert(x / y <= x);
	}
	/* mod_nonneg + mod_lt_divisor + mod_le */
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (1 <= y) {
			assert(x % y <= y - 1);
			assert(x % y <= x);
		}
	}
}

/* ---------------- ShiftOptBranchSel (common/axioms_shift_opt.h) -------- */

/*
 * Branch-selection facts for the shift family's op-optimality proofs.
 * `m` ranges over the two supported masks only, so op_bits(m) is 32 or
 * 64 and both cases are enumerated explicitly rather than left nondet.
 */
static void shift_opt_family(void)
{
	/* lsr_sign_clear: m in {2^32-1, 2^64-1}, 0 <= v <= m>>1 ==>
	   ((uint64_t)v >> (op_bits(m) - 1)) == 0
	   (the CONVERSE of lsr_sign_any; (uint64_t)v is WP's to_uint64(v)) */
	{
		int64_t v = nondet_i64();
		if (0 <= v && v <= (int64_t)(0xFFFFFFFFULL >> 1))
			assert(((uint64_t)v >> (32 - 1)) == 0);
	}
	{
		int64_t v = nondet_i64();
		if (0 <= v && v <= (int64_t)(ALL1 >> 1))
			assert(((uint64_t)v >> (64 - 1)) == 0);
	}
	/* len2mask_shift_u: 0 <= q < op_bits(m) ==>
	   (2^64-1) >> (64 - (op_bits(m) - q)) == m >> q */
	{
		uint64_t q = nondet_u64();
		if (q < 32)
			assert((ALL1 >> (unsigned)(64 - (32 - q))) ==
			       (0xFFFFFFFFULL >> (unsigned)q));
	}
	{
		uint64_t q = nondet_u64();
		if (q < 64)
			assert((ALL1 >> (unsigned)(64 - (64 - q))) ==
			       (ALL1 >> (unsigned)q));
	}
	/* len2mask_shift_s is a WP-PROVED lemma, not a trusted axiom; checked
	   here anyway since it costs nothing and guards against a later
	   restatement drifting into an axiom. 0 <= q <= op_bits(m) - 2 ==>
	   (2^64-1) >> (64 - (op_bits(m) - q - 1)) == (m >> 1) >> q */
	{
		uint64_t q = nondet_u64();
		if (q <= 30)
			assert((ALL1 >> (unsigned)(64 - (32 - q - 1))) ==
			       ((0xFFFFFFFFULL >> 1) >> (unsigned)q));
	}
	{
		uint64_t q = nondet_u64();
		if (q <= 62)
			assert((ALL1 >> (unsigned)(64 - (64 - q - 1))) ==
			       ((ALL1 >> 1) >> (unsigned)q));
	}
	/* to_signed_canon_rt (also a WP-PROVED lemma, checked for the same
	   reason): -(m>>1)-1 <= w <= m>>1 ==> to_signed(((uint64_t)w)&m, m) == w,
	   with to_signed(v,m) = v <= (m>>1) ? v : v - (m+1). */
	{
		int64_t w = nondet_i64();
		if (-(int64_t)(0xFFFFFFFFULL >> 1) - 1 <= w &&
		    w <= (int64_t)(0xFFFFFFFFULL >> 1)) {
			uint64_t p = ((uint64_t)w) & 0xFFFFFFFFULL;
			int64_t dec = (p <= (0xFFFFFFFFULL >> 1)) ? (int64_t)p
				: (int64_t)p - (int64_t)(0xFFFFFFFFULL + 1);
			assert(dec == w);
		}
	}
	{
		/* m == 2^64-1: m+1 is 2^64, outside uint64, but the decode
		   `p - 2^64` for p >= 2^63 is exactly the int64 reading of p,
		   so (int64_t)p IS to_signed(p, ALL1). */
		int64_t w = nondet_i64();
		uint64_t p = ((uint64_t)w) & ALL1;
		assert((int64_t)p == w);
	}
}

/* ---------------- trusted function contracts (common/shared.h) --------- */

static void rte_clz64_contract(void)
{
	/* rte_clz64 (WP sees contract-only prototype): v != 0 ==>
	   0 <= result <= 63 && (v >> (63 - result)) == 1.
	   Checked against the real builtin, which CBMC models bit-exactly. */
	uint64_t v = nondet_u64();
	if (v != 0) {
		unsigned int r = (unsigned int)__builtin_clzll(v);
		assert(r <= 63);
		assert((v >> (63 - r)) == 1);
	}
}

int main(void)
{
	land_family();
	land_wrap_family();
	bpf_arg_ptr_type();
	lenshift_core();
	lenshift_width();
	lenshift_signed();
	arshshift();
	clz_window();
	land_canon();
	lor_bounds();
	lxor_bounds();
	mul_bounds();
	divmod_bounds();
	shift_opt_family();
	rte_clz64_contract();
	return 0;
}
