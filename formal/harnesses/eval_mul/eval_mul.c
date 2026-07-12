#include "eval_mul.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"
/* Nonlinear-multiply facts (monotonicity, overflow bounds) needed by THIS
 * proof; include from the .c, not the header. */
#include "../../common/axioms_mul.h"

#ifdef FIX_MUL_SCONST
/*
 * Sign-extend the low-opsz-bit pattern p (in [0, msk]) to its signed
 * value — the C computation of to_signed(p, msk). For msk = 2^w - 1,
 * p <= msk>>1 keeps p; otherwise p - (msk + 1). msk + 1 wraps to 0 for
 * the 64-bit mask, so (int64_t)(p - 0) == (int64_t)p correctly
 * reinterprets a set top bit as negative.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t mul_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}
#endif

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	requires \separated(rd, rs);
	requires is_scalar_or_pointer(rs->v.type) && is_scalar_or_pointer(rd->v.type);
	requires range_validity(rd, msk) && range_validity(rs, msk);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar_or_pointer(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_mul_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_mul_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_mul(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* both operands are constants */
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		rd->u.min = (rd->u.min * rs->u.min) & msk;
		rd->u.max = (rd->u.max * rs->u.max) & msk;
	/* check for overflow */
#ifdef FIX_MUL_UGUARD
	/*
	 * Upstream tests `rs->u.max <= msk >> opsz`, not `>> opsz / 2` like
	 * the rd side. For opsz == 64 that is `msk >> 64` — shift-by-width
	 * UB that evaluates to msk on shift-masking hardware (x86/ARM), so
	 * the guard vanishes and the 64-bit product overflows; for
	 * opsz == 32 it is `msk >> 32 == 0`, making the fast path all but
	 * dead. Both operands must be < 2^(w/2) for the product to fit in w
	 * bits. BMC witness (upstream): opsz 64, rd.u.max 2^32-1,
	 * rs.u.max 2^32 -> product wraps, tracked u.max under-approximates.
	 */
	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz / 2) {
#else
	} else if (rd->u.max <= msk >> opsz / 2 && rs->u.max <= msk >> opsz) {
#endif
		/* monotonicity stone: mul_mono fires here (only preconditions
		 * in scope) but not inside the folded ordering/soundness goals */
		/*@ assert u_mono: (rd->u.min * rs->u.min) <= (rd->u.max * rs->u.max); */
		rd->u.max *= rs->u.max;
		rd->u.min *= rs->u.min;
	} else
		eval_umax_bound(rd, msk);

	/* both operands are constants */
	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
#ifdef FIX_MUL_SCONST
		/*
		 * Upstream stores the raw masked product pattern in s.min/s.max
		 * without sign-extending: when the low-w product has its sign
		 * bit set (e.g. opsz == 32, 2^30 * 2 -> 0x80000000) the tracked
		 * value is a large positive instead of the true negative,
		 * breaking swidth and ssound. Sign-extend to the canonical
		 * signed value.
		 */
		rd->s.min = mul_sext(((uint64_t)rd->s.min * (uint64_t)rs->s.min) & msk, msk);
		rd->s.max = mul_sext(((uint64_t)rd->s.max * (uint64_t)rs->s.max) & msk, msk);
#else
		rd->s.min = ((uint64_t)rd->s.min * (uint64_t)rs->s.min) & msk;
		rd->s.max = ((uint64_t)rd->s.max * (uint64_t)rs->s.max) & msk;
#endif
	/* check that both operands are positive and no overflow */
#ifdef FIX_MUL_SGUARD
	/*
	 * Upstream has NO overflow guard here: `rd->s.max *= rs->s.max` on
	 * int64 overflows (signed-overflow UB for 64-bit; exceeds msk>>1 in
	 * every non-trivial case), so the tracked s.max leaves the signed
	 * width and range ordering can invert (ESBMC witness). Require both
	 * maxima below 2^((w-1)/2) so the product stays <= msk>>1:
	 * (msk>>1) >> (opsz/2) is 0x7FFF (opsz 32) / 0x7FFFFFFF (opsz 64),
	 * and B*B <= msk>>1 in both.
	 */
	} else if (rd->s.min >= 0 && rs->s.min >= 0 &&
			rd->s.max <= (msk >> 1) >> (opsz / 2) &&
			rs->s.max <= (msk >> 1) >> (opsz / 2)) {
#else
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
#endif
		/*@ assert s_mono: (rd->s.min * rs->s.min) <= (rd->s.max * rs->s.max); */
		rd->s.max *= rs->s.max;
		rd->s.min *= rs->s.min;
	} else
		eval_smax_bound(rd, msk);
}
