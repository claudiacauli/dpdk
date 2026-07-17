#include "eval_or.h"
#include "../eval_uor_max/eval_uor_max.h"
#include "../eval_smax_bound/eval_smax_bound.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
#include "../../common/axioms_or.h"
#include "../../common/axioms_and.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	requires \separated(rd, rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns rd->u, rd->s;

	ensures unchanged_v:    rd->v == \old(rd->v);
	ensures unchanged_mask: rd->mask == \old(rd->mask);
	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:     eval_or_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_or_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_or(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/*
	 * WP stepping stones, all asserted HERE — before any call — where
	 * only the preconditions are in scope (after a call, eval_uor_max's
	 * uor_cover quantifier cascades on any fresh lor node a stone
	 * introduces and the stone itself times out).
	 *
	 * mask_ite bridges the callee's opsz-keyed ite bounds to msk;
	 * uw_* pull the width bounds out of range_within_width as their own
	 * small goals (also the eval_uor_max call-site preconditions).
	 */
	/*@ assert mask_ite: msk == (opsz == 32 ? 0xFFFFFFFF : 0xFFFFFFFFFFFFFFFF); */
	/*@ assert uw_d: rd->u.max <= msk; */
	/*@ assert uw_s: rs->u.max <= msk; */
	/*@ assert sw_d: (uint64_t)rd->s.max <= (msk >> 1) || rd->s.max < 0; */
	/*@ assert sw_s: (uint64_t)rs->s.max <= (msk >> 1) || rs->s.max < 0; */
	/*
	 * Sign-consistency stones for the ssound quantifier, which ranges y
	 * over os.u: when rs is non-negative its unsigned pattern range IS
	 * its signed value range, and when rs is a constant that range is the
	 * single masked pattern. Asserted pre-call, from range_validity's
	 * sign_consistency; the ssound parts consume them as hypotheses.
	 */

	/* both operands are constants */
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		/*@ assert uw_or_c: (rd->u.max | rs->u.max) <= msk; */
		rd->u.min |= rs->u.min;
		rd->u.max |= rs->u.max;
	} else {
		rd->u.max = eval_uor_max(rd->u.max, rs->u.max, opsz);
		rd->u.min = RTE_MAX(rd->u.min, rs->u.min);
	}

	/* both operands are constants */
	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
		/* signed OR of two canonical w-bit values stays canonical */
		/*@ assert sw_or_c:
		      -(msk >> 1) - 1 <= (rd->s.max | rs->s.max) &&
		      (rd->s.max | rs->s.max) <= (msk >> 1); */
		rd->s.min |= rs->s.min;
		rd->s.max |= rs->s.max;

	/* both operands are non-negative */
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
		/* both s.max non-negative and <= msk>>1: uor_half bounds the
		 * result under msk>>1 (swidth); each side is a lower bound on
		 * the OR, so the RTE_MAX of the mins still fits below it (sord) */
		/*@ assert bn_half_d: (uint64_t)rd->s.max <= (msk >> 1); */
		/*@ assert bn_half_s: (uint64_t)rs->s.max <= (msk >> 1); */
		rd->s.max = eval_uor_max(rd->s.max, rs->s.max, opsz);
		rd->s.min = RTE_MAX(rd->s.min, rs->s.min);
	} else
		eval_smax_bound(rd, msk);
}
