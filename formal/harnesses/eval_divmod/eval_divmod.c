#include "eval_divmod.h"
#include "../eval_smax_bound/eval_smax_bound.h"
/* Axioms are included from the .c (and not the header) so consumers of
 * the contract don't drag them into their own PO search spaces. */
#include "axioms_div.h"

#ifdef FIX_DIVMOD_SIGNED_32
/*
 * Sign-extend the low-w-bit pattern p (in [0, msk]) to its canonical
 * signed value — the C computation of to_signed(p, msk). Same helper as
 * eval_mul's mul_sext: for msk = 2^w - 1, p <= msk>>1 keeps p; otherwise
 * p - (msk + 1), where msk + 1 wraps to 0 for the 64-bit mask and
 * (int64_t)(p - 0) correctly reinterprets a set top bit as negative.
 */
/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires 0 <= p <= msk;
	assigns \nothing;
	ensures \result == to_signed(p, msk);
*/
static int64_t dm_sext(uint64_t p, uint64_t msk)
{
	return (p <= (msk >> 1)) ? (int64_t)p : (int64_t)(p - (msk + 1));
}
#endif

/*@
	requires op == BPF_DIV || op == BPF_MOD;
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	requires \separated(rd, rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	// The validator rejects exactly the constant-zero divisor; on that
	// path rd is left untouched (the caller propagates the error and the
	// program is refused).
	ensures err_iff:   (\result != \null) <==>
		(\old(rd->u.min) == \old(rd->u.max) &&
		 \old(rs->u.min) == \old(rs->u.max) && \old(rs->u.max) == 0);
	ensures err_frame: \result != \null ==>
		rd->u == \old(rd->u) && rd->s == \old(rd->s);

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     \result == \null ==>
		eval_divmod_unsigned_soundness(op, \old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     \result == \null ==>
		eval_divmod_signed_soundness(op, \old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (divmod-optimal). Soundness above is UNCONDITIONAL; this is
	// op-optimal on the CONSTANT-OPERAND branch, where both endpoints are computed
	// exactly and each witnesses itself via self_optimal.
	//
	// THE RANGE BRANCH IS NOT OP-OPTIMAL, and an earlier draft of this contract
	// got that wrong. It guarded on `op == BPF_MOD || rs.u.min == 1`, on the
	// reasoning that MOD's u.max = min(rd.u.max, rs.u.max - 1) is the tight
	// remainder bound and only DIV is loose. Both halves are refuted by exhaustive
	// small-domain enumeration (scratch check over rd,rs in [0,20]):
	//   - MOD, rd = [1,1], rs = [2,3]: code gives [0,1], true image is [1,1].
	//   - DIV with rs.u.min == 1, rd = [1,2], rs = [1,1]: code [0,2], true [1,2].
	// 12015 MOD cases and 1520 rs.u.min==1 DIV cases are loose in that domain
	// alone. The dominant cause is structural: the range branch sets u.min = 0
	// UNCONDITIONALLY, but 0 is in the image only when some representable pair
	// divides exactly (MOD) or has x < y (DIV) -- usually neither. MOD's u.max is
	// independently loose too (rd = [10,12], rs = [7,7]: bound 6, true max 5).
	//
	// So the range branch needs a genuine precision fix before it can carry an
	// op-optimality clause -- a tight u.min, and for DIV the tight u.max
	// rd.u.max / rs.u.min. That is its own project (optimality_notes.md); stating a
	// guard here that merely dodges the counterexamples would be fiction.
	ensures uopt: \result == \null &&
		self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.min) == \old(rd->u.max) && \old(rs->u.min) == \old(rs->u.max)
			==> eval_divmod_unsigned_optimal(op, \old(*rd), \old(*rs), *rd, msk);
	ensures sopt: \result == \null &&
		self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rd->u.min) == \old(rd->u.max) && \old(rs->u.min) == \old(rs->u.max)
			==> eval_divmod_signed_optimal(op, \old(*rd), \old(*rs), *rd, msk);
*/
const char *
eval_divmod(uint32_t op, struct bpf_reg_val *rd, struct bpf_reg_val *rs,
	uint64_t msk)
{
	/* both operands are constants */
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		if (rs->u.max == 0)
			return "division by 0";
		if (op == BPF_DIV) {
			rd->u.min /= rs->u.min;
			rd->u.max /= rs->u.max;
		} else {
			rd->u.min %= rs->u.min;
			rd->u.max %= rs->u.max;
		}
	} else {
		if (op == BPF_MOD)
			rd->u.max = RTE_MIN(rd->u.max, rs->u.max - 1);
		else
			rd->u.max = rd->u.max;
		rd->u.min = 0;
	}

#ifdef FIX_DIVMOD_SIGNED_32
	/*
	 * Upstream tests sign-contiguity of the new unsigned range against
	 * the 64-BIT signed boundaries (INT64_MIN/INT64_MAX) and reuses the
	 * raw patterns as the signed bounds, INDEPENDENT of msk. For
	 * msk == 2^32-1 the test is always true (u.max <= 0xFFFFFFFF <=
	 * INT64_MAX), so a pattern above 0x7FFFFFFF is stored as a large
	 * POSITIVE signed bound: swidth breaks and ssound with it — the
	 * value's canonical signed reading to_signed(p, msk) is negative.
	 * BMC witness: 32-bit DIV, rd = [0x80000000, 0x80000000],
	 * rs = [1, 1] -> s = [2^31, 2^31], true value -2^31. Test against
	 * the mask's own sign boundary and sign-extend the endpoints; for
	 * msk == 2^64-1 this coincides exactly with the original.
	 *
	 * Violates (unfixed): swidth, ssound — WP no-fixes run (exactly
	 * those two ensures fail, 0/1 each; uord/sord/uwidth/usound all
	 * still prove) and ESBMC BMC_32 witness (range_within_width).
	 */
	if (rd->u.min > (msk >> 1) || rd->u.max <= (msk >> 1)) {
		rd->s.min = dm_sext(rd->u.min, msk);
		rd->s.max = dm_sext(rd->u.max, msk);
	} else
#else
	if (rd->u.min >= (uint64_t)INT64_MIN || rd->u.max <= (uint64_t)INT64_MAX) {
		/*
		 * All values have the same sign bit, which means range
		 * contiguous as unsigned is also contiguous as signed,
		 * so we can just reuse it without any changes.
		 */
		rd->s.min = rd->u.min;
		rd->s.max = rd->u.max;
	} else
#endif
		eval_smax_bound(rd, msk);

	return NULL;
}
