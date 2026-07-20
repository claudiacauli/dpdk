#include "eval_rsh.h"
#include "../../common/axioms_shift_opt.h"
/*
 * DO NOT REMOVE — this include looks unused and is not. Nothing in this file
 * explicitly needs to_signed_canon_rt (the sopt guard forces s.min >= 0, where
 * the pattern round-trip is the identity), but the lemma is load-bearing for
 * ssound anyway: with it, ssound proves 3/3 in ~51s; without it, 2/3 with part3
 * timing out at 600s. Measured both ways, twice each, on an idle machine.
 * Lemmas are hypotheses TU-wide, so dropping one can move a cliff goal.
 */
#include "../../common/lemmas_canon.h"
#include "../eval_max_bound/eval_max_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"

/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires opsz == op_bits(msk);
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap. WP's typed memory model would otherwise
	// admit partial overlaps no C caller can produce, under which the
	// stores to rd->u clobber the rs->u reads below (see eval_lsh.c).
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
	ensures usound:     eval_rsh_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_rsh_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (rsh-optimal). Logical right shift: the unsigned track NEVER
	// widens (shifting right only shrinks), so its only guard is shift < width;
	// the signed track additionally needs a non-negative s.min (a negative one
	// widens via eval_smax_bound). Anti-monotone in the shift -> CROSSED corners:
	// u.max <- (rd.u.max, rs.u.min), u.min <- (rd.u.min, rs.u.max). self_optimal
	// supplies the corner un_witnesses forming the bin_witness.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk)
			==> eval_rsh_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		\old(rs->u.max) < op_bits(msk) && \old(rd->s.min) >= 0
			==> eval_rsh_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_rsh(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, size_t opsz,
	uint64_t msk)
{
	/* check if shift value is less then max result bits */
	if (rs->u.max >= opsz) {
		eval_max_bound(rd, msk);
		/*@ assert full_slo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert full_shi: rd->s.max == (int64_t)(msk >> 1); */
		return;
	}

	/*@ assert in_ord_d: rd->u.min <= rd->u.max; */
	/*@ assert in_ord_s: rs->u.min <= rs->u.max; */
	rd->u.max >>= rs->u.min;
	rd->u.min >>= rs->u.max;


	/* check that dreg values are always positive */
	if ((uint64_t)rd->s.min >> (opsz - 1) != 0) {
		eval_smax_bound(rd, msk);
		/*@ assert sfull_lo: rd->s.min == -(int64_t)(msk >> 1) - 1; */
		/*@ assert sfull_hi: rd->s.max == (int64_t)(msk >> 1); */
	}
	else {
		/*@ assert s_in_ord: rd->s.min <= rd->s.max; */
		/*@ assert smin_nonneg: 0 <= rd->s.min; */
		rd->s.max >>= rs->u.min;
		rd->s.min >>= rs->u.max;
		/*@ assert smax_shift_id:
		      rd->s.max == \at(rd->s.max, Pre) >> \at(rs->u.min, Pre); */
		/*@ assert smin_shift_id:
		      rd->s.min == \at(rd->s.min, Pre) >> \at(rs->u.max, Pre); */
		/*@ assert sopt_sum_smax:
		      \at(rd->s.min,Pre) >= 0 ==>
		        to_signed((((uint64_t)\at(rd->s.max,Pre)) & msk)
		                  >> \at(rs->u.min,Pre), msk) == rd->s.max; */
		/*@ assert sopt_sum_smin:
		      \at(rd->s.min,Pre) >= 0 ==>
		        to_signed((((uint64_t)\at(rd->s.min,Pre)) & msk)
		                  >> \at(rs->u.max,Pre), msk) == rd->s.min; */
	}

	/* OP-OPTIMALITY witnesses, as ground instances. self_optimal gives each
	 * operand un_witness at its own endpoints, so the CROSSED corner pairs are
	 * bin_witnesses; the _sum_ goals say those corners shift to the stored
	 * endpoints. The u track needs no frame step -- nothing below the shifts
	 * writes rd->u (the signed branch touches only rd->s). */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        (\at(rd->u.max,Pre) >> \at(rs->u.min,Pre)) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rs->u.max,Pre) < op_bits(msk) ==>
	        (\at(rd->u.min,Pre) >> \at(rs->u.max,Pre)) == rd->u.min; */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    \at(rs->u.min,Pre), msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    \at(rs->u.max,Pre), msk); */

	/* BRANCH SELECTION for the signed track. The sopt guard `s.min >= 0` has
	 * to rule out the eval_smax_bound widening above, whose condition is
	 * `(uint64_t)s.min >> (opsz - 1) != 0`. That reduces to "a non-negative
	 * in-range value has its sign bit clear" -- true, but a symbolic-amount
	 * shift fact, so it comes from the trusted lsr_sign_clear axiom
	 * (common/axioms_shift_opt.h). Without it the branch-local sopt_sum_
	 * facts below cannot survive the merge to where the ensures is
	 * evaluated. (The u track needs no such stone: rsh never widens it.) */
	/*@ assert sopt_branch_sel:
	      \at(rd->s.min,Pre) >= 0 ==>
	        (((uint64_t)\at(rd->s.min,Pre)) >> (opsz - 1)) == 0; */

	/* Post-merge restatement of the in-branch sopt_sum_ stones: same facts,
	 * now in the state the ensures is evaluated in. Provable only with
	 * sopt_branch_sel above to select the non-widening branch. */
	/*@ assert sopt_sum_end_smax:
	      \at(rd->s.min,Pre) >= 0 ==>
	        to_signed((((uint64_t)\at(rd->s.max,Pre)) & msk)
	                  >> \at(rs->u.min,Pre), msk) == rd->s.max; */
	/*@ assert sopt_sum_end_smin:
	      \at(rd->s.min,Pre) >= 0 ==>
	        to_signed((((uint64_t)\at(rd->s.min,Pre)) & msk)
	                  >> \at(rs->u.max,Pre), msk) == rd->s.min; */
}
