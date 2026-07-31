
#include <stdint.h>
#include <assert.h>

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
unsigned __int128 nondet_u128(void);

#define ALL1 0xFFFFFFFFFFFFFFFFULL

static void land_family(void)
{
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		assert((x & y) <= y);
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		assert((x & y) <= x);
	}
	{
		uint64_t x = nondet_u64();
		assert((x & ALL1) == x);
	}
	{
		uint64_t x = nondet_u64();
		if (x <= 0xFFFFFFFFULL)
			assert((x & 0xFFFFFFFFULL) == x);
	}
}

static void land_wrap_family(void)
{

	{
		uint64_t x = nondet_u64();
		if (0xFFFFFFFFULL < x && x <= 2 * 0xFFFFFFFFULL)
			assert((x & 0xFFFFFFFFULL) == x - 0x100000000ULL);
	}

	{
		unsigned __int128 x = nondet_u128();
		if ((unsigned __int128)ALL1 < x &&
		    x <= (unsigned __int128)2 * ALL1)
			assert((x & (unsigned __int128)ALL1) ==
			       x - ((unsigned __int128)1 << 64));
	}

	{
		uint64_t x = nondet_u64();
		if (x >= 0xFFFFFFFF00000000ULL)
			assert((x & 0xFFFFFFFFULL) ==
			       x - 0xFFFFFFFF00000000ULL);
	}
}

static void apply_mask_block_family(void)
{
	{
		uint64_t x = nondet_u64();
		assert(x == (x & 0xFFFFFFFF00000000ULL) + (x & 0xFFFFFFFFULL));
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (x <= y)
			assert((x & 0xFFFFFFFF00000000ULL) <=
			       (y & 0xFFFFFFFF00000000ULL));
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if ((x & 0xFFFFFFFF00000000ULL) < (y & 0xFFFFFFFF00000000ULL))
			assert((x & 0xFFFFFFFF00000000ULL) + 0x100000000ULL <=
			       (y & 0xFFFFFFFF00000000ULL));
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64(), z = nondet_u64();
		if (x <= z && z <= y &&
		    (x & 0xFFFFFFFF00000000ULL) == (y & 0xFFFFFFFF00000000ULL)) {
			assert((z & 0xFFFFFFFF00000000ULL) ==
			       (x & 0xFFFFFFFF00000000ULL));
			assert((x & 0xFFFFFFFFULL) <= (z & 0xFFFFFFFFULL));
			assert((z & 0xFFFFFFFFULL) <= (y & 0xFFFFFFFFULL));
		}
	}
	{
		uint64_t x = nondet_u64();
		assert(((x & 0xFFFFFFFF00000000ULL) & 0xFFFFFFFFULL) == 0);
	}
	{
		uint64_t x = nondet_u64();
		if (0x100000000ULL <= (x & 0xFFFFFFFF00000000ULL))
			assert((((x & 0xFFFFFFFF00000000ULL) - 1) &
				0xFFFFFFFFULL) == 0xFFFFFFFFULL);
	}

	{
		uint64_t x = nondet_u64();
		assert((x & 0xFFFFFFFF00000000ULL) ==
		       0x100000000ULL * (x / 0x100000000ULL));
	}
}

static void bpf_arg_ptr_type(void)
{

	int64_t t = nondet_i64();
	if ((t & 0x10) != 0)
		assert(t != 0 && t != 1);
	else
		assert(t != 0x10 && t != 0x11 && t != 0x12);
}

static void lenshift_core(void)
{

	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (y <= 64) {
			unsigned __int128 p = (unsigned __int128)x << y;
			assert(p >= 0);
		}
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), y = nondet_u64();
		if (a <= b && y <= 64)
			assert(((unsigned __int128)a << y) <=
			       ((unsigned __int128)b << y));
	}
	{
		uint64_t x = nondet_u64(), p = nondet_u64(), q = nondet_u64();
		if (p <= q && q <= 64)
			assert(((unsigned __int128)x << p) <=
			       ((unsigned __int128)x << q));
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && p <= q && q <= 64)
			assert(((unsigned __int128)a << p) <=
			       ((unsigned __int128)b << q));
	}
	{
		uint64_t x = nondet_u64(), k = nondet_u64(), w = nondet_u64();
		if (k <= w && w <= 64 &&
		    x <= (((unsigned __int128)1 << (w - k)) - 1))
			assert(((unsigned __int128)x << k) <=
			       ((unsigned __int128)1 << w) - 1);
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (y <= 64)
			assert((y == 64 ? 0 : x >> y) <= x);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), y = nondet_u64();
		if (a <= b && y <= 63)
			assert((a >> y) <= (b >> y));
	}
	{
		uint64_t x = nondet_u64(), p = nondet_u64(), q = nondet_u64();
		if (p <= q && q <= 63)
			assert((x >> q) <= (x >> p));
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && p <= q && q <= 63)
			assert((a >> q) <= (b >> p));
	}
}

static void lenshift_width(void)
{

	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k < 32 && x <= (ALL1 >> (unsigned)(64 - (32 - k))))
			assert(((unsigned __int128)x << k) <= 0xFFFFFFFFULL);
	}

	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k < 64 && k >= 1 && x <= (ALL1 >> (unsigned)k))
			assert(((unsigned __int128)x << k) <= ALL1);
		if (k == 0)
			assert(((unsigned __int128)x << k) <= ALL1);
	}
}

static void lenshift_signed(void)
{

	{
		int64_t v = nondet_i64();
		uint64_t w = nondet_u64();
		if (31 <= w && w <= 63 && (((uint64_t)v >> w) == 0))
			assert(0 <= v);
	}
	{
		uint64_t k = nondet_u64();
		if (1 <= k && k <= 63)
			assert((ALL1 >> k) <= 0x7FFFFFFFFFFFFFFFULL);
	}
	{
		uint64_t k = nondet_u64();
		if (33 <= k && k <= 63)
			assert((ALL1 >> k) <= 0x7FFFFFFFULL);
	}

	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k <= 30 &&
		    x < (ALL1 >> (unsigned)(64 - (32 - k - 1))))
			assert(((unsigned __int128)x << k) <= 0x7FFFFFFFULL);
	}

	{
		uint64_t x = nondet_u64(), k = nondet_u64();
		if (k <= 62 &&
		    x < (ALL1 >> (unsigned)(64 - (64 - k - 1))))
			assert(((unsigned __int128)x << k) <=
			       0x7FFFFFFFFFFFFFFFULL);
	}
}

static void arshshift(void)
{
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		uint64_t y = nondet_u64();
		if (a <= b && y <= 63)
			assert((a >> y) <= (b >> y));
	}
	{
		int64_t x = nondet_i64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (x < 0 && p <= q && q <= 63)
			assert((x >> p) <= (x >> q));
	}
	{
		int64_t x = nondet_i64();
		uint64_t y = nondet_u64();
		if (x < 0 && y <= 63)
			assert(x <= (x >> y) && (x >> y) <= -1);
	}
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		uint64_t p = nondet_u64(), q = nondet_u64();
		if (a <= b && b < 0 && p <= q && q <= 63)
			assert((a >> p) <= (b >> q));
	}

	{
		int64_t v = nondet_i64();
		if (-0x80000000LL <= v && v < 0x80000000LL)
			assert((int64_t)((uint64_t)v << 32) ==
			       v * 0x100000000LL);
	}

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

static void clz_window(void)
{
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1)
			assert(v <= (ALL1 >> r));
	}
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1)
			assert(((ALL1 >> r) >> 1) < v);
	}
	{
		uint64_t r = nondet_u64();
		if (r <= 63)
			assert(((ALL1 >> r) & ((ALL1 >> r) + 1)) == 0);
	}
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 && v <= 0xFFFFFFFFULL)
			assert((ALL1 >> r) <= 0xFFFFFFFFULL);
	}
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 && v <= 0x7FFFFFFFULL)
			assert((ALL1 >> r) <= 0x7FFFFFFFULL);
	}
	{
		uint64_t v = nondet_u64(), r = nondet_u64();
		if (r <= 63 && (v >> (63 - r)) == 1 &&
		    v <= 0x7FFFFFFFFFFFFFFFULL)
			assert((ALL1 >> r) <= 0x7FFFFFFFFFFFFFFFULL);
	}
}

static void land_canon(void)
{
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a & b) &&
			       (a & b) <= 0x7FFFFFFFLL);
	}

	{
		__int128 a = nondet_i64(), b = nondet_i64();
		__int128 r = a & b;
		assert(-((__int128)1 << 63) <= r &&
		       r <= ((__int128)1 << 63) - 1);
	}

	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t m1 = nondet_u64(), m2 = nondet_u64();
		if (a <= m1 && b <= m2 &&
		    (m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0)
			assert((a & b) <= (m1 & m2));
	}
	{
		uint64_t x = nondet_u64(), m = nondet_u64();
		if (x <= m && (m & (m + 1)) == 0)
			assert((x & m) == x);
	}

	{
		__int128 a = nondet_i64();
		uint64_t b = nondet_u64();
		__int128 r = a & (__int128)b;
		assert(0 <= r && r <= (__int128)b);
	}
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
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), m = nondet_u64();
		if (a <= m && (m & (m + 1)) == 0)
			assert((a & b) <= m);
	}

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

	{
		int64_t u = nondet_i64();
		__int128 p = (__int128)u & (__int128)0xFFFFFFFFFFFFFFFFULL;
		__int128 half = (__int128)0x7FFFFFFFFFFFFFFFULL;
		__int128 dec = (p <= half) ? p : p - ((__int128)1 << 64);
		assert(dec == (__int128)u);
	}

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

	{
		uint64_t p64 = nondet_u64(), q64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		__int128 m = ms[k], half = m >> 1, p = p64, q = q64;
		if (p <= m && q <= m) {
			__int128 land_pq = p & q;
			__int128 lhs = (land_pq <= half) ? land_pq
							 : land_pq - (m + 1);
			__int128 dec_p = (p <= half) ? p : p - (m + 1);
			__int128 dec_q = (q <= half) ? q : q - (m + 1);
			assert(lhs == (dec_p & dec_q));
		}
	}
}

static void land_and_canon_gaps(void)
{

	{
		int64_t w = nondet_i64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, ALL1 };
		int k = nondet_int() ? 1 : 0;
		__int128 m = (__int128)ms[k];
		__int128 half = m >> 1;
		if (-half - 1 <= (__int128)w && (__int128)w <= half) {
			unsigned __int128 pat = ((unsigned __int128)(__int128)w) &
						(unsigned __int128)m;
			__int128 dec = (pat <= (unsigned __int128)half)
				? (__int128)pat
				: (__int128)pat - (m + 1);
			assert(dec == (__int128)w);
		}
	}

	{
		uint64_t v = nondet_u64(), y = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, ALL1 };
		int k = nondet_int() ? 1 : 0;
		uint64_t m = ms[k];
		if (v <= m)
			assert((v & y) == (v & (y & m)));
	}
}

static void lor_bounds(void)
{
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a | b) >= 0);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert(a <= (a | b) && b <= (a | b));
	}
	{
		uint64_t a = nondet_u64();
		assert((a | 0) == a && (0 | a) == a);
	}
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a | b) &&
			       (a | b) <= 0x7FFFFFFFLL);
	}

	{
		int64_t a = nondet_i64(), b = nondet_i64();
		int64_t r = a | b;
		assert(INT64_MIN <= r && r <= INT64_MAX);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64(), m = nondet_u64();
		assert(((a | (b & m)) & m) == ((a | b) & m));
	}

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

	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t m1 = nondet_u64(), m2 = nondet_u64();
		if (a <= m1 && b <= m2 &&
		    (m1 & (m1 + 1)) == 0 && (m2 & (m2 + 1)) == 0)
			assert((a | b) <= (m1 | m2));
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0xFFFFFFFFULL && b <= 0xFFFFFFFFULL)
			assert((a | b) <= 0xFFFFFFFFULL);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a | b) <= ALL1);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0x7FFFFFFFULL && b <= 0x7FFFFFFFULL)
			assert((a | b) <= 0x7FFFFFFFULL);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0x7FFFFFFFFFFFFFFFULL && b <= 0x7FFFFFFFFFFFFFFFULL)
			assert((a | b) <= 0x7FFFFFFFFFFFFFFFULL);
	}
}

static void lxor_bounds(void)
{
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) >= 0);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) <= (a | b));
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		if (a <= 0xFFFFFFFFULL && b <= 0xFFFFFFFFULL)
			assert((a ^ b) <= 0xFFFFFFFFULL);
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		assert((a ^ b) <= ALL1);
	}
	{
		int64_t a = nondet_i64(), b = nondet_i64();
		if (-0x80000000LL <= a && a <= 0x7FFFFFFFLL &&
		    -0x80000000LL <= b && b <= 0x7FFFFFFFLL)
			assert(-0x80000000LL <= (a ^ b) &&
			       (a ^ b) <= 0x7FFFFFFFLL);
	}

	{
		int64_t a = nondet_i64(), b = nondet_i64();
		int64_t r = a ^ b;
		assert(INT64_MIN <= r && r <= INT64_MAX);
	}

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

static void mul_bounds(void)
{

	{
		uint64_t v64 = nondet_u64(), w64 = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		unsigned __int128 m = (unsigned __int128)ms[k];
		unsigned __int128 half = m >> 1, v = v64, w = w64;
		if (v <= m && w <= m) {
			__int128 c = (v <= half) ? (__int128)v
						 : (__int128)v - ((__int128)m + 1);
			__int128 e = (w <= half) ? (__int128)w
						 : (__int128)w - ((__int128)m + 1);
			unsigned __int128 pv = ((unsigned __int128)v *
						(unsigned __int128)w) & m;
			unsigned __int128 pc = ((unsigned __int128)((__int128)c *
						(__int128)e)) & m;
			__int128 dv = (pv <= half) ? (__int128)pv
						   : (__int128)pv - ((__int128)m + 1);
			__int128 dc = (pc <= half) ? (__int128)pc
						   : (__int128)pc - ((__int128)m + 1);
			assert(dv == dc);
		}
	}
	{
		uint64_t a = nondet_u64(), b = nondet_u64();
		uint64_t ms[2] = { 0xFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL };
		int k = nondet_int() ? 1 : 0;
		unsigned __int128 m = (unsigned __int128)ms[k];
		uint64_t wrapped = a * b;
		unsigned __int128 lhs = (unsigned __int128)(wrapped & (uint64_t)m);
		unsigned __int128 prod = (unsigned __int128)a * b;
		unsigned __int128 rhs = prod & m;
		assert(lhs == rhs);
	}
}

static void land_mod_family(void)
{

	{
		uint64_t x = nondet_u64();
		assert((x & 0xFFFFFFFFULL) == x % 0x100000000ULL);
		assert((uint32_t)x == x % 0x100000000ULL);
	}
	{
		unsigned __int128 p = nondet_u128();
		unsigned __int128 m64 = (unsigned __int128)ALL1 + 1;
		assert((p & (unsigned __int128)ALL1) == p % m64);
		assert((uint64_t)p == (uint64_t)(p % m64));
	}

	{
		uint64_t x = nondet_u64();
		__int128 negx = -(__int128)x;
		uint64_t low = x & 0xFFFFFFFFULL;
		__int128 expect = (low == 0) ? 0 : (__int128)0x100000000LL - low;
		assert((uint32_t)negx == (uint32_t)expect);
	}
}

static void mul_ssound_folded(void)
{

	{
		uint64_t ms[2] = { 0xFFFFFFFFULL, ALL1 };
		int k = nondet_int() ? 1 : 0;
		unsigned __int128 m = (unsigned __int128)ms[k];
		unsigned __int128 half = m >> 1;
		int64_t dsmin = nondet_i64(), dsmax = nondet_i64();
		int64_t ssmin = nondet_i64(), ssmax = nondet_i64();
		int64_t wsmin = nondet_i64(), wsmax = nondet_i64();
		uint64_t dumin = nondet_u64(), dumax = nondet_u64();
		uint64_t sumin = nondet_u64(), sumax = nondet_u64();
		uint64_t v64 = nondet_u64(), w64 = nondet_u64();
		__int128 dv = ((unsigned __int128)v64 <= half)
			? (__int128)v64 : (__int128)v64 - ((__int128)m + 1);
		__int128 dw = ((unsigned __int128)w64 <= half)
			? (__int128)w64 : (__int128)w64 - ((__int128)m + 1);
		if (0 <= dsmin && dsmin <= dsmax && 0 <= ssmin && ssmin <= ssmax &&
		    (__int128)wsmin <= (__int128)dsmin * ssmin &&
		    (__int128)dsmax * ssmax <= (__int128)wsmax &&
		    (__int128)dsmax * ssmax <= (__int128)half &&
		    dumin <= v64 && v64 <= dumax &&
		    (__int128)dsmin <= dv && dv <= (__int128)dsmax &&
		    sumin <= w64 && w64 <= sumax &&
		    (__int128)ssmin <= dw && dw <= (__int128)ssmax) {
			unsigned __int128 p = ((unsigned __int128)v64 *
					       (unsigned __int128)w64) & m;
			__int128 dp = (p <= half) ? (__int128)p
						  : (__int128)p - ((__int128)m + 1);
			assert((__int128)wsmin <= dp && dp <= (__int128)wsmax);
		}
	}

	{
		uint64_t ms[2] = { 0xFFFFFFFFULL, ALL1 };
		int k = nondet_int() ? 1 : 0;
		unsigned __int128 m = (unsigned __int128)ms[k];
		unsigned __int128 half = m >> 1;
		int64_t dsmin = nondet_i64(), dsmax = nondet_i64();
		int64_t ssmin = nondet_i64(), ssmax = nondet_i64();
		int64_t wsmin = nondet_i64(), wsmax = nondet_i64();
		uint64_t dumin = nondet_u64(), dumax = nondet_u64();
		uint64_t sumin = nondet_u64(), sumax = nondet_u64();
		uint64_t v64 = nondet_u64(), w64 = nondet_u64();
		__int128 dv = ((unsigned __int128)v64 <= half)
			? (__int128)v64 : (__int128)v64 - ((__int128)m + 1);
		__int128 dw = ((unsigned __int128)w64 <= half)
			? (__int128)w64 : (__int128)w64 - ((__int128)m + 1);
		unsigned __int128 cp = ((unsigned __int128)((__int128)dsmin *
					(__int128)ssmin)) & m;
		__int128 dcp = (cp <= half) ? (__int128)cp
					    : (__int128)cp - ((__int128)m + 1);
		if ((unsigned __int128)dumax <= m && (unsigned __int128)sumax <= m &&
		    dsmin == dsmax && ssmin == ssmax &&
		    (__int128)wsmin <= dcp && dcp <= (__int128)wsmax &&
		    dumin <= v64 && v64 <= dumax &&
		    (__int128)dsmin <= dv && dv <= (__int128)dsmax &&
		    sumin <= w64 && w64 <= sumax &&
		    (__int128)ssmin <= dw && dw <= (__int128)ssmax) {
			unsigned __int128 p = ((unsigned __int128)v64 *
					       (unsigned __int128)w64) & m;
			__int128 dp = (p <= half) ? (__int128)p
						  : (__int128)p - ((__int128)m + 1);
			assert((__int128)wsmin <= dp && dp <= (__int128)wsmax);
		}
	}
}

static void divmod_bounds(void)
{

	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (1 <= y)
			assert(x / y <= x);
	}
	{
		uint64_t x = nondet_u64(), y = nondet_u64();
		if (1 <= y) {
			assert(x % y <= y - 1);
			assert(x % y <= x);
		}
	}
}

static void shift_opt_family(void)
{

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

		int64_t w = nondet_i64();
		uint64_t p = ((uint64_t)w) & ALL1;
		assert((int64_t)p == w);
	}
}

static void rte_clz64_contract(void)
{

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
	apply_mask_block_family();
	bpf_arg_ptr_type();
	lenshift_core();
	lenshift_width();
	lenshift_signed();
	arshshift();
	clz_window();
	land_canon();
	land_and_canon_gaps();
	lor_bounds();
	lxor_bounds();
	mul_bounds();
	land_mod_family();
	mul_ssound_folded();
	divmod_bounds();
	shift_opt_family();
	rte_clz64_contract();
	return 0;
}
