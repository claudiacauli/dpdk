#include "eval_lsh.h"
#include "../../common/axioms_shift_opt.h"
/*
 * NOT common/lemmas_canon.h: that header's to_signed_canon_rt was
 * tried here (2026-07-20) on the theory that lsh's ssound conclusion
 * is its round-trip shape — the goal dump refuted it (the lsl sits
 * between the two lands, so the trigger can never unify; nothing
 * changed with the include). The lsh-shaped lemma below is the one
 * whose application term matches the actual PO.
 */
#include "lemmas_canon_lsh.h"
#include "../eval_max_bound/eval_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap. WP's typed memory model would otherwise
	// admit partial overlaps (rs == rd +/- a few words) that no C caller
	// can produce with two distinct struct objects; under such overlap the
	// stores to rd->u clobber the rs->u reads below and the ordering
	// ensures become falsifiable in-model. (The BMC harness likewise
	// forces prs = &rs; see eval_lsh_bmc.c.)
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
	ensures usound:     eval_lsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_lsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (lsh-optimal). Monotone in value AND shift, so each endpoint is
	// the extreme (value, shift) corner -- UNCROSSED, unlike rsh: u.max <-
	// (rd.u.max, rs.u.max), u.min <- (rd.u.min, rs.u.min). Soundness above is
	// UNCONDITIONAL; op-optimality holds from SELF-OPTIMAL operands in the NO-WIDEN
	// regime (shift < width AND no overflow -- none of eval_max_bound /
	// eval_umax_bound / eval_smax_bound fires). self_optimal supplies the corner
	// un_witnesses that form the bin_witness the existentials need.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) &&
		\old(rd->u.max) <= (msk >> \old(rs->u.max))
			==> eval_lsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	// The signed guard mirrors the code's signed overflow test exactly, and is
	// NOT the unsigned guard with an extra conjunct:
	//   - the shift bound is `<= op_bits - 2`, not `< op_bits`. At
	//     q == op_bits - 1 the code's threshold collapses to the ternary's 0
	//     branch, so any s.max >= 0 widens -- and s.min >= 0 forces s.max >= 0.
	//     That corner is therefore never op-optimal and must be excluded.
	//   - the value bound is STRICT. The code widens on `s.max >= threshold`,
	//     so no-widen needs `s.max < threshold`; a `<=` here would admit the
	//     equality case, which widens and is not op-optimal.
	// No unsigned conjunct is needed: eval_umax_bound assigns only rv->u, so
	// the unsigned widening branch cannot disturb the signed track.
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) <= op_bits(msk) - 2 &&
		\old(rd->s.min) >= 0 &&
		\old(rd->s.max) < ((msk >> 1) >> \old(rs->u.max))
			==> eval_lsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_lsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* check if shift value is less then max result bits */
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		/*@ assert full_slo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert full_shi: rd->s.max == (int64_t)(msk >> 1); */
		return;
	}

	/* check for overflow */
	if (rd->u.max > RTE_LEN2MASK(opsz - rs->u.max, uint64_t))
		eval_umax_bound(rd, msk);
	else {
		/*@ assert in_ord_d: rd->u.min <= rd->u.max; */
		/*@ assert in_ord_s: rs->u.min <= rs->u.max; */
		/*@ assert min_fits: rd->u.min <= RTE_LEN2MASK(opsz - rs->u.min, uint64_t); */
		/*
		 * usound stones (2026-07-20, dump-diagnosed): the no-overflow
		 * guard's width fact exists only in the C-emitted size_t-wrap
		 * shape, while lsl_width_32/64 / len2mask_shift_u trigger on
		 * the ACSL LEN2MASK node — nothing links the two e-nodes, and
		 * usound parts 07/10/11 spin inventing the strip. max_fits
		 * transports the guard onto the ACSL node (min_fits' twin,
		 * same spot, needs strictly less); max_shift_fits then follows
		 * by lsl_width firing on it, handing the big POs the ground
		 * fact `lsl(u.max, q.max) <= msk` they were missing.
		 */
		/*@ assert max_fits: rd->u.max <= RTE_LEN2MASK(opsz - rs->u.max, uint64_t); */
		/*@ assert max_shift_fits: (rd->u.max << rs->u.max) <= msk; */
		rd->u.max <<= rs->u.max;
		rd->u.min <<= rs->u.min;
		/*@ assert umin_stone: rd->u.min <= msk; */
		/*@ assert uwidth_stone: rd->u.max <= msk; */
		/* uopt _sum_ stones, stated HERE where the no-overflow guard of this
		 * branch is live and the context is small (cf. eval_rsh: the same facts
		 * stated only at function end time out). Restated post-merge below. */
		/*@ assert uopt_sum_umax:
		      ((\at(rd->u.max,Pre) << \at(rs->u.max,Pre)) & msk) == rd->u.max; */
		/*@ assert uopt_sum_umin:
		      ((\at(rd->u.min,Pre) << \at(rs->u.min,Pre)) & msk) == rd->u.min; */
	}

	/* check that dreg values are and would remain always positive */
	if ((uint64_t)rd->s.min >> (opsz - 1) != 0 || rd->s.max >=
			(rs->u.max == opsz - 1 ? 0 :
				 RTE_LEN2MASK(opsz - rs->u.max - 1, int64_t))) {
		eval_smax_bound(rd, msk);
		/*@ assert sfull_lo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert sfull_hi: rd->s.max == (int64_t)(msk >> 1); */
	}
	else {
		/*@ assert s_in_ord: rd->s.min <= rd->s.max; */
		/*@ assert sq_ord: rs->u.min <= rs->u.max; */
		/*@ assert smin_nonneg: 0 <= rd->s.min; */
		rd->s.max <<= rs->u.max;
		rd->s.min <<= rs->u.min;
		/*@ assert swidth_stone: rd->s.max <= (int64_t)(msk >> 1); */
		/*@ assert smax_shift_id:
		      rd->s.max == \at(rd->s.max, Pre) << \at(rs->u.max, Pre); */
		/*@ assert smin_shift_id:
		      rd->s.min == \at(rd->s.min, Pre) << \at(rs->u.min, Pre); */
		/* sopt _sum_ stones, in-branch (same rationale as uopt's above). */
		/*@ assert sopt_sum_smax:
		      to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk)
		                 << \at(rs->u.max,Pre)) & msk, msk) == rd->s.max; */
		/*@ assert sopt_sum_smin:
		      to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk)
		                 << \at(rs->u.min,Pre)) & msk, msk) == rd->s.min; */
	}

	/* OP-OPTIMALITY witnesses (ground instances). lsh is monotone in BOTH value
	 * and shift, so the corners are UNCROSSED. self_optimal gives each operand
	 * un_witness at its own endpoints -> the corner pairs are bin_witnesses. */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    \at(rs->u.max,Pre), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    \at(rs->u.min,Pre), msk); */

	/* BRANCH SELECTION. Both tracks widen through a guard the ensures'
	 * no-overflow hypothesis is meant to exclude, but the guards are written
	 * with RTE_LEN2MASK while the hypotheses are written with msk -- and
	 * reconciling the two is a symbolic-amount shift identity WP cannot do.
	 * The two facts come from common/axioms_shift_opt.h: len2mask_shift_u
	 * (trusted axiom) and len2mask_shift_s (WP-proved lemma). Without them
	 * the in-branch _sum_ stones cannot survive the merge. */
	/*@ assert uopt_branch_sel:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        RTE_LEN2MASK(opsz - \at(rs->u.max,Pre), uint64_t)
	          == (msk >> \at(rs->u.max,Pre)); */
	/*@ assert sopt_branch_sel_sign:
	      \at(rd->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.min,Pre)) >> (opsz - 1)) == 0; */
	/*@ assert sopt_branch_sel_thr:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 ==>
	        RTE_LEN2MASK(opsz - \at(rs->u.max,Pre) - 1, int64_t)
	          == ((msk >> 1) >> \at(rs->u.max,Pre)); */

	/* Post-merge restatements of the in-branch _sum_ stones, in the state the
	 * ensures is evaluated in. Provable only with the branch-selection stones
	 * above. */
	/*@ assert uopt_sum_end_umax:
	      \at(rs->u.max,Pre) < op_bits(msk) &&
	      \at(rd->u.max,Pre) <= (msk >> \at(rs->u.max,Pre)) ==>
	        ((\at(rd->u.max,Pre) << \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_end_umin:
	      \at(rs->u.max,Pre) < op_bits(msk) &&
	      \at(rd->u.max,Pre) <= (msk >> \at(rs->u.max,Pre)) ==>
	        ((\at(rd->u.min,Pre) << \at(rs->u.min,Pre)) & msk) == rd->u.min; */
	/*@ assert sopt_sum_end_smax:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 &&
	      \at(rd->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) < ((msk >> 1) >> \at(rs->u.max,Pre)) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk)
	                   << \at(rs->u.max,Pre)) & msk, msk) == rd->s.max; */
	/*@ assert sopt_sum_end_smin:
	      \at(rs->u.max,Pre) <= op_bits(msk) - 2 &&
	      \at(rd->s.min,Pre) >= 0 &&
	      \at(rd->s.max,Pre) < ((msk >> 1) >> \at(rs->u.max,Pre)) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk)
	                   << \at(rs->u.min,Pre)) & msk, msk) == rd->s.min; */
}
