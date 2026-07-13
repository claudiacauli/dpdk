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
	ensures usound:     eval_and_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_and_signed_soundness(\old(*rd), \old(*rs), *rd, msk);
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
	/*@ assert pat_s: rs->s.min >= 0 ==>
	      rs->u.max == (uint64_t)rs->s.max; */
	/*@ assert pat_c: rs->s.min == rs->s.max ==>
	      rs->u.max == ((uint64_t)rs->s.max & msk); */

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
		/*@ assert c_pat_s: rs->u.max == ((uint64_t)rs->s.max & msk); */
		rd->s.min &= rs->s.min;
		rd->s.max &= rs->s.max;
#ifdef FIX_AND_SIGNED_GUARD
	/* both operands non-negative: both s.max-derived masks are covers */
	} else if (rd->s.min >= 0 && rs->s.min >= 0) {
		/*@ assert bn_half_d: (uint64_t)rd->s.max <= (msk >> 1); */
		/*@ assert bn_half_s: (uint64_t)rs->s.max <= (msk >> 1); */
		/*@ assert bn_pat_s: rs->u.max == (uint64_t)rs->s.max; */
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
}
