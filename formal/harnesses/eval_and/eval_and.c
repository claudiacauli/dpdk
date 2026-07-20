#include "eval_and.h"
#include "../eval_uand_max/eval_uand_max.h"
#include "../eval_smax_bound/eval_smax_bound.h"
/* Axioms are include from the .c (and not the header) so consumers of the
   contract don't drag them into their own PO search spaces. Do NOT move
   this include to the header or it will slow down verification. */
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
	ensures usound:     eval_and_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_and_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY: NOT achievable (Category B -- optimality_notes.md §6d).
	// u.max = eval_uand_max(rd.u.max, rs.u.max) = umax_bits(v1) & umax_bits(v2) is
	// a bit-FILL bound; the tight max(a&b) over two intervals depends on the
	// achievable BIT PATTERNS, not the endpoints (even min(rd.u.max,rs.u.max) is
	// loose -- disjoint bits -> true max 0), so there is NO endpoint formula and no
	// op-optimality ensures. A tight bound needs a bit-level interval-AND algorithm
	// (O(width)). BMC-confirmed loose (eval_and_opt_bmc.c). Soundness UNCONDITIONAL.
	//
	// ...BUT there is a narrow regime where the bit-fill bound IS attained, and
	// that regime is stateable. Derived and brute-forced exhaustively over 6-bit
	// operands (4.32M interval pairs, 105k guard firings, ZERO violations):
	//
	//   the computed bound is attained  <==>  it lies INSIDE BOTH input ranges,
	//
	// because then x = y = bound is an available pair and bound & bound == bound.
	// Both halves matter: requiring only `bound <= u.max` is FALSE -- counterexample
	// rd=[0,1], rs=[2,2] gives bound 1 <= 1 and 1 <= 2, yet 1 is not in rs's range
	// at all and the true max is 0.
	//
	// The guard is phrased on the OUTPUT endpoint rather than on uand_max(...),
	// which is what lets this be stated WITHOUT a logic counterpart for the
	// bit-fill helpers -- rd->u.max post IS the computed bound.
	//
	// Stating it as plain interval containment is NOT enough: eval_and does not
	// require range_agreement (only ordering + within_width), so nothing links the
	// u-range to the s-range, while bin_witness demands BOTH. self_optimal does not
	// close the gap either -- it constrains the four endpoints, not an interior
	// point like the bound. So the guard is phrased with un_witness directly, which
	// is exactly the cross-track condition needed:
	//
	//   each output endpoint is itself representable in BOTH input registers
	//
	// and then x = y = that endpoint is an available pair whose AND is the endpoint
	// itself, by idempotence. One shape covers both endpoints and both branches
	// (constant and bit-fill) rather than special-casing u.min == 0.
	//
	// GATED behind PROVE_OPTIMALITY (2026-07-20): the witness stones these
	// ensures need are `assert`s, i.e. hypotheses of EVERY later PO, and
	// their ground land nodes on the u-endpoints seed the TU-scoped
	// land-axiom family's e-matching inside the usound/ssound searches --
	// diagnosed as what tipped monolithic usound and the 3 hardest ssound
	// parts past the ceiling. The driver proves uopt/sopt + stones in a
	// dedicated -DPROVE_OPTIMALITY cell; the soundness cell compiles
	// without, restoring the clean context. BACKLOG C5 tracks the
	// permanent folded-lemma form.
#ifdef PROVE_OPTIMALITY
	ensures uopt:
		un_witness(\old(*rd), rd->u.max, msk) &&
		un_witness(\old(*rs), rd->u.max, msk) &&
		un_witness(\old(*rd), rd->u.min, msk) &&
		un_witness(\old(*rs), rd->u.min, msk)
			==> eval_and_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);

	// Signed twin. Same idea, one extra step: the witness for a signed endpoint
	// E is the PATTERN of E paired with itself, and recovering E from it needs
	// the encode/decode round-trip to_signed(E & msk, msk) == E, valid because
	// swidth puts both output endpoints in the canonical window.
	//
	// TERM SHAPE MATTERS HERE. The round-trip exists in this corpus twice:
	// to_signed_pattern_id (axioms_and.h, shape `w & m`, ALREADY in scope via the
	// include above) and to_signed_canon_rt (lemmas_canon.h, shape `((uint64_t)w) & m`,
	// NOT included here). The guard is therefore written `rd->s.max & msk`, the
	// unwrapped shape, so the in-scope axiom can fire. Writing the cast form would
	// silently fail to trigger.
	ensures sopt:
		un_witness(\old(*rd), rd->s.max & msk, msk) &&
		un_witness(\old(*rs), rd->s.max & msk, msk) &&
		un_witness(\old(*rd), rd->s.min & msk, msk) &&
		un_witness(\old(*rs), rd->s.min & msk, msk)
			==> eval_and_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
#endif
*/
void eval_and(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz, uint64_t msk)
{
	/*
	 * WP stepping stones: pull the width bounds out of
	 * range_within_width here, as their own small goals — the
	 * eval_uand_max call-site requires otherwise need the predicate
	 * unfolding AND the len2mask lemma chain inside one large search.
	 */
	/*@ assert uw_d: rd->u.max <= msk; */
	/*@ assert uw_s: rs->u.max <= msk; */
	/*
	 * Conditional identity stones for the signed branches, asserted
	 * HERE — before any call — on purpose: after a call, the
	 * uand_cover ensures' quantifier cascades on the fresh land node a
	 * masking-identity goal introduces, and the stone itself times
	 * out. In this pre-call PO there is nothing but preconditions and
	 * the chain closes. ssound's signed parts consume these as
	 * hypotheses.
	 */
	/*@ assert id_d: rd->s.min >= 0 ==>
	      ((uint64_t)rd->s.max & (msk >> 1)) == (uint64_t)rd->s.max; */
	/*@ assert id_s: rs->s.min >= 0 ==>
	      ((uint64_t)rs->s.max & (msk >> 1)) == (uint64_t)rs->s.max; */

	/* both operands are constants */
	if (rd->u.min == rd->u.max && rs->u.min == rs->u.max) {
		rd->u.min &= rs->u.min;
		rd->u.max &= rs->u.max;
	} else {
		rd->u.max = eval_uand_max(rd->u.max, rs->u.max, opsz);
		rd->u.min = 0;
	}

	/* both operands are constants */
	if (rd->s.min == rd->s.max && rs->s.min == rs->s.max) {
		/*
		 * WP stepping stones (here and in the branches below): each
		 * names one link of the ssound chain — the pattern/value
		 * consistency of the rs side, and the msk>>1 maskings being
		 * no-ops on in-range values — as its own small goal, instead
		 * of the ensures having to re-derive the composition.
		 */
		rd->s.min &= rs->s.min;
		rd->s.max &= rs->s.max;
#ifdef FIX_AND_SIGNED_GUARD
	/* both operands non-negative: both s.max-derived masks are covers */
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
		/*@ assert bn_half_d: (uint64_t)rd->s.max <= (msk >> 1); */
		/*@ assert bn_half_s: (uint64_t)rs->s.max <= (msk >> 1); */
		rd->s.max = eval_uand_max(rd->s.max & (msk >> 1),
			rs->s.max & (msk >> 1), opsz);
		rd->s.min = 0;
	/*
	 * Only ONE operand guaranteed non-negative: the result of & is
	 * still non-negative, but only that operand's mask covers it — the
	 * other side's s.max says nothing about its bit PATTERNS (a
	 * negative or sign-spanning register has patterns far above its
	 * s.max). Upstream builds the bound from BOTH masks here, capping
	 * the estimate unsoundly. BMC counterexample: msk64, rs spanning
	 * the sign boundary with small s.max -> tracked s.max 2^48-1 while
	 * the true result reaches bit 56. Bound by the non-negative side
	 * against a full-width unknown instead.
	 */
	} else if (rd->s.min >= 0 || rs->s.min >= 0) {
		int64_t nn = (rd->s.min >= 0) ? rd->s.max : rs->s.max;
		/*@ assert os_nn_nonneg: 0 <= nn; */
		/*@ assert os_nn_half: (uint64_t)nn <= (msk >> 1); */
		rd->s.max = eval_uand_max((uint64_t)nn & (msk >> 1),
			msk >> 1, opsz);
		rd->s.min = 0;
#else
	/* at least one of operand is non-negative */
	} else if (rd->s.min >= 0 || rs->s.min >= 0) {
		rd->s.max = eval_uand_max(rd->s.max & (msk >> 1),
			rs->s.max & (msk >> 1), opsz);
		rd->s.min = 0;
#endif
	} else
		eval_smax_bound(rd, msk);

#ifdef PROVE_OPTIMALITY
	/*
	 * OP-OPTIMALITY witness stone. uopt is an EXISTENTIAL and WP will not
	 * invent x,y; under the guard the witness for each endpoint is that
	 * endpoint paired with itself, so the only fact the ensures still needs
	 * is idempotence of & on the two output endpoints. Named here as its own
	 * small goal rather than left inside the quantifier search.
	 *
	 * The whole block is gated with the uopt/sopt ensures: as `assert`s
	 * these stones are assumed by every later PO, and their ground land
	 * nodes on the u-endpoints seed the land-axiom family inside the
	 * soundness searches (see the contract comment).
	 */
	/*@ assert uopt_idem_max: (rd->u.max & rd->u.max) == rd->u.max; */
	/*@ assert uopt_idem_min: (rd->u.min & rd->u.min) == rd->u.min; */

	/*
	 * sopt chain, named link by link. swidth is an ensures, and ensures are
	 * NOT hypotheses of one another in WP, so the canonical-window facts the
	 * round-trip axiom needs have to be re-established here as their own goals.
	 */
	/*@ assert sopt_half_max: -(msk >> 1) - 1 <= rd->s.max <= (msk >> 1); */
	/*@ assert sopt_half_min: -(msk >> 1) - 1 <= rd->s.min <= (msk >> 1); */
	/*@ assert sopt_rt_max: to_signed(rd->s.max & msk, msk) == rd->s.max; */
	/*@ assert sopt_rt_min: to_signed(rd->s.min & msk, msk) == rd->s.min; */
	/*@ assert sopt_idem_max:
	      ((rd->s.max & msk) & (rd->s.max & msk)) == (rd->s.max & msk); */
	/*@ assert sopt_idem_min:
	      ((rd->s.min & msk) & (rd->s.min & msk)) == (rd->s.min & msk); */
#endif
}
