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

	// OP-OPTIMALITY: NOT achievable (Category B -- optimality_notes.md §6d).
	// u.max = eval_uor_max(rd.u.max, rs.u.max) = umax_bits(v1) | umax_bits(v2), a
	// bit-FILL bound; the all-ones fill is reached only by bit-aligned inputs, so
	// max(a|b) has no endpoint formula and no op-optimality ensures. BMC-confirmed
	// loose (eval_or_opt_bmc.c). Soundness above stays UNCONDITIONAL.
	//
	// ...BUT the regime where the bit-fill bound IS attained is stateable, by the
	// same construction proved for eval_and: if an output endpoint is itself
	// representable in BOTH inputs, then x = y = that endpoint is an available
	// pair, and OR (like AND) is IDEMPOTENT, so it reproduces the endpoint.
	// un_witness rather than plain interval containment because eval_or does not
	// require range_agreement either, and bin_witness constrains both tracks.
	ensures uopt:
		un_witness(\old(*rd), rd->u.max, msk) &&
		un_witness(\old(*rs), rd->u.max, msk) &&
		un_witness(\old(*rd), rd->u.min, msk) &&
		un_witness(\old(*rs), rd->u.min, msk)
			==> eval_or_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);

	// Signed twin: witness is the PATTERN of each endpoint, recovered through
	// to_signed_pattern_id (axioms_and.h, in scope above). Unwrapped `& msk`
	// shape deliberately -- the cast form would need lemmas_canon.h and would
	// silently fail to trigger.
	ensures sopt:
		un_witness(\old(*rd), rd->s.max & msk, msk) &&
		un_witness(\old(*rs), rd->s.max & msk, msk) &&
		un_witness(\old(*rd), rd->s.min & msk, msk) &&
		un_witness(\old(*rs), rd->s.min & msk, msk)
			==> eval_or_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
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
	 * agreement; the ssound parts consume them as hypotheses.
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

	/* Optimality witness stones: idempotence of | on each output endpoint,
	 * plus the canonical-window facts the round-trip axiom needs (swidth is
	 * an ensures, and ensures are not hypotheses of one another). */
	/*@ assert uopt_idem_max: (rd->u.max | rd->u.max) == rd->u.max; */
	/*@ assert uopt_idem_min: (rd->u.min | rd->u.min) == rd->u.min; */
	/*@ assert sopt_half_max: -(msk >> 1) - 1 <= rd->s.max <= (msk >> 1); */
	/*@ assert sopt_half_min: -(msk >> 1) - 1 <= rd->s.min <= (msk >> 1); */
	/*@ assert sopt_rt_max: to_signed(rd->s.max & msk, msk) == rd->s.max; */
	/*@ assert sopt_rt_min: to_signed(rd->s.min & msk, msk) == rd->s.min; */
	/*@ assert sopt_idem_max:
	      ((rd->s.max & msk) | (rd->s.max & msk)) == (rd->s.max & msk); */
	/*@ assert sopt_idem_min:
	      ((rd->s.min & msk) | (rd->s.min & msk)) == (rd->s.min & msk); */
}
