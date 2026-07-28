#include "eval_add.h"
#include "../eval_fill_max_bound/eval_fill_max_bound.h"
#include "../eval_umax_bound/eval_umax_bound.h"
#include "../eval_smax_bound/eval_smax_bound.h"


/*@
	requires msk == _32_BIT_MASK || msk == _64_BIT_MASK;
	requires \valid(rd) && \valid(rs);
	// The real caller (eval_alu) always passes rs as a fresh local copy,
	// so rd and rs never overlap — even for `add rX, rX`. WP's typed
	// memory model would otherwise admit partial overlaps no C caller
	// can produce; this replaces the former `admit sep_else` (same fact,
	// but proved against the caller contract instead of trusted mid-body).
	requires \separated(rd, rs);
	requires is_scalar(rs->v.type) && is_scalar(rd->v.type);
	requires range_ordering(rd) && range_ordering(rs);
	requires range_within_width(rd, msk) && range_within_width(rs, msk);
	terminates \true;
	assigns *rd;

	ensures type_ok:    is_scalar(rd->v.type);
	ensures uord:       unsigned_range_ordering(rd);
	ensures sord:       signed_range_ordering(rd);
	ensures uwidth:     unsigned_range_within_width(rd, msk);
	ensures swidth:     signed_range_within_width(rd, msk);
	ensures usound:	    eval_add_unsigned_soundness(\old(*rd), \old(*rs), *rd, msk);
	ensures ssound:     eval_add_signed_soundness(\old(*rd), \old(*rs), *rd, msk);

	// OP-OPTIMALITY (add-optimal). Soundness above is UNCONDITIONAL. Witness for
	// each endpoint is the corresponding input-corner PAIR: self_optimal(rd)
	// supplies un_witness at rd.u.max/u.min and self_optimal(rs) at rs.u.max/u.min,
	// which is exactly the bin_witness the existential needs.
	//
	// With the carry-parity overflow tests in the body (FIX_ADD_UNSIGNED_OVFL /
	// FIX_ADD_SIGNED_OVFL_OPT) the guard weakens from NO-overflow to UNIFORM
	// overflow -- both corners in the same wrap regime (equal carry bits / equal
	// underflow-overflow trits). Under it the kept output endpoints ARE the masked
	// corner sums, attained by the corner pairs self_optimal supplies. That is the
	// MAXIMAL corner-witness regime, NOT unconditional: when the corners wrap
	// differently the body widens to top, and top's endpoints are INTERIOR points
	// that the intersection gamma need not contain -- brute-refuted at W=3/4
	// (scratchpad brute_opt_fixes.c, e.g. neg of u[1,4]s[-4,1], gamma={1,4}); the
	// guarded forms below are brute-CLEAN at W=3/4 with ~1.5x the unsigned coverage
	// of the old no-overflow guard (brute_guarded.c). The arc/boundary argument
	// that would make top attained holds for single-track interval semantics only.
	// SINGLE CONTRACT OF RECORD (fixed semantics): under --no-fixes these two
	// clauses go red on the both-wrap regime -- that red documents the upstream
	// imprecision the FIX_ADD_*_OVFL body fixes repair.
	ensures uopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->u.min) + \old(rs->u.min) > msk) <==>
		 (\old(rd->u.max) + \old(rs->u.max) > msk))
			==> eval_add_unsigned_optimal(\old(*rd), \old(*rs), *rd, msk);
	ensures sopt: self_optimal(\old(*rd), msk) && self_optimal(\old(*rs), msk) &&
		((\old(rd->s.min) + \old(rs->s.min) < -(int64_t)(msk >> 1) - 1) <==>
		 (\old(rd->s.max) + \old(rs->s.max) < -(int64_t)(msk >> 1) - 1)) &&
		((\old(rd->s.min) + \old(rs->s.min) > (int64_t)(msk >> 1)) <==>
		 (\old(rd->s.max) + \old(rs->s.max) > (int64_t)(msk >> 1)))
			==> eval_add_signed_optimal(\old(*rd), \old(*rs), *rd, msk);
*/
void eval_add(struct bpf_reg_val *rd, const struct bpf_reg_val *rs, uint64_t msk)
{
	struct bpf_reg_val rs_buf;
	struct bpf_reg_val rv;

	if (RTE_BPF_ARG_PTR_TYPE(rs->v.type) != 0) {
		if (RTE_BPF_ARG_PTR_TYPE(rd->v.type) != 0) {
			/* treat sum of pointers as sum of two unknown scalars */
			eval_fill_max_bound(&rs_buf, msk);
			*rd = rs_buf;
			rs = &rs_buf;
		} else {
			/* scalar + pointer is a pointer of the same type */
			rd->v = rs->v;
		}
	}

	rv.u.min = (rd->u.min + rs->u.min) & msk;
	rv.u.max = (rd->u.max + rs->u.max) & msk;
	/*
	 * uopt stepping stone. Under the no-overflow guard the corner sums do not
	 * wrap, so `& msk` is the identity here; that in turn makes the overflow
	 * test below false, pinning the stored u endpoints to the corner sums --
	 * exactly the witnesses eval_add_unsigned_optimal quantifies over. Asserted
	 * here, where only the guard and the preconditions are in scope.
	 */
	/*@ assert uopt_nowrap:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        (rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre)); */
	rv.s.min = ((uint64_t)rd->s.min + (uint64_t)rs->s.min) & msk;
	rv.s.max = ((uint64_t)rd->s.max + (uint64_t)rs->s.max) & msk;

	#ifdef FIX_ADD_SIGNED_32
		/*
		* For 32-bit ops the masked sums above live in [0, 2^32) (the
		* signed value zero-extended), while rd/rs signed bounds and the
		* eval_smax_bound() reset use the sign-extended representation
		* ([INT32_MIN, INT32_MAX]). The overflow check below compares the
		* two representations directly, so a negative bound that wraps to
		* a large positive masked value can slip past it and leave
		* s.min > s.max. Canonicalize to the sign-extended form *before*
		* the check so both sides speak the same language.
		*/
		if (msk == _32_BIT_MASK) {
			/*
			* WP stepping stones. Every rung below is load-bearing:
			* - *_rng before the sext: bound the masked value so the
			*   provers can strip the opaque to_sint64 store-wrapper
			*   (via land_le_mask); the land_* axiom triggers cannot
			*   fire through it otherwise.
			* - mask32_*: fold `& msk` into a piecewise-linear
			*   wrap-offset fact (land_id_u32 / land_wrap_u32_top).
			* - *_rng after the sext: canonical-int32 bounds; they
			*   pin the unique in-range case of sext32_*_val for ord
			*   and discharge the 32-bit half of swidth.
			* - sext32_*_val: the congruence interface ord consumes;
			*   downstream goals are pure linear arithmetic and never
			*   unfold `&` or the to_{u,s}int* conversions again.
			*/
			/*@ assert mask32_min_rng: 0 <= rv.s.min <= 0xFFFFFFFF; */
			/*@ assert mask32_max_rng: 0 <= rv.s.max <= 0xFFFFFFFF; */
			/*@ assert mask32_min:
			      rv.s.min == rd->s.min + rs->s.min ||
			      rv.s.min == rd->s.min + rs->s.min + 0x100000000; */
			/*@ assert mask32_max:
			      rv.s.max == rd->s.max + rs->s.max ||
			      rv.s.max == rd->s.max + rs->s.max + 0x100000000; */
			rv.s.min = (int32_t)(uint32_t)rv.s.min;
			rv.s.max = (int32_t)(uint32_t)rv.s.max;
			/*@ assert sext32_min_rng: INT32_MIN <= rv.s.min <= INT32_MAX; */
			/*@ assert sext32_max_rng: INT32_MIN <= rv.s.max <= INT32_MAX; */
			/*@ assert sext32_min_val:
			      rv.s.min == rd->s.min + rs->s.min ||
			      rv.s.min == rd->s.min + rs->s.min - 0x100000000 ||
			      rv.s.min == rd->s.min + rs->s.min + 0x100000000; */
			/*@ assert sext32_max_val:
			      rv.s.max == rd->s.max + rs->s.max ||
			      rv.s.max == rd->s.max + rs->s.max - 0x100000000 ||
			      rv.s.max == rd->s.max + rs->s.max + 0x100000000; */
		}
	#endif

	/*
	 * sopt stepping stones, the signed twins of uopt_nowrap. Placed AFTER the
	 * 32-bit canonicalization so both widths speak the sign-extended language:
	 * for msk32 the sext32_*_val disjunctions above plus the no-overflow guard
	 * exclude the +/-2^32 wrap cases; for msk64 the two's-complement sum is the
	 * mathematical sum outright. Split per endpoint to keep each goal small.
	 */
	/*@ assert sopt_nowrap_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre); */
	/*@ assert sopt_nowrap_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre); */
#ifdef FIX_ADD_SIGNED_OVFL_OPT
	/* Sign helpers, the key the wrap stones' cast chains need: under
	 * both-OVERFLOW every operand bound is non-negative (b > SMAX_w - other
	 * >= 0 since the other is within width), so the uint64 casts are
	 * transparent; under both-UNDERFLOW every bound is negative. Pure linear
	 * from the width requires -- but the provers do not invent the inference
	 * inside the larger goals (both _min wrap stones spun a full 3000s
	 * ceiling in isolation without these, 2026-07-21). */
	/*@ assert sopt_of_signs:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        0 <= \at(rd->s.min,Pre) && 0 <= \at(rs->s.min,Pre); */
	/*@ assert sopt_uf_signs:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        \at(rd->s.max,Pre) < 0 && \at(rs->s.max,Pre) < 0; */
	/* 64-bit value pins, the msk64 counterpart of sext32_*_val above: the
	 * to_sint64/to_uint64 chain collapses to a +/-2^64 wrap-offset
	 * disjunction (split-probe 2026-07-21: exactly the one msk64 part of
	 * ofwrap_min was the spinning residue -- the 32-bit parts close on the
	 * sext32 stones, the 64-bit part had no value pin at all). */
	/*@ assert sext64_min_val: msk == _64_BIT_MASK ==>
	      (rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) ||
	       rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) - 0x10000000000000000 ||
	       rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) + 0x10000000000000000); */
	/*@ assert sext64_max_val: msk == _64_BIT_MASK ==>
	      (rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) ||
	       rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) - 0x10000000000000000 ||
	       rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) + 0x10000000000000000); */
	/* Uniform-wrap twins of sopt_nowrap_*. Both-OVERFLOW: the min corner sum
	 * already exceeds SMAX_w, hence so does the max corner's; every masked sum
	 * re-reads as sum - (msk+1). Both-UNDERFLOW mirror: the max corner sum is
	 * below SMIN_w; every masked sum re-reads as sum + (msk+1). Linear per
	 * endpoint, same placement discipline as the no-wrap pair. */
	/*@ assert sopt_ofwrap_min:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_ofwrap_max:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_ufwrap_min:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) + msk + 1; */
	/*@ assert sopt_ufwrap_max:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) + msk + 1; */
#endif

	/*
	 * if at least one of the operands is not constant,
	 * then check for overflow
	 */
#ifdef FIX_ADD_UNSIGNED_OVFL
	/*
	 * Optimal unsigned overflow handling. `rv.u.X < rd->u.X` is exactly the
	 * carry-out bit of corner X (the masked sum dropped below the addend iff it
	 * crossed a 2^w boundary). The masked corner-sum interval is the EXACT
	 * reachable set precisely when both corners carry the SAME amount -- a
	 * uniform wrap slides the whole band down by 2^w without splitting it. The
	 * corners carrying DIFFERENT amounts is the only case the band straddles the
	 * 0 / 2^w seam, and there no single interval beats [0,msk] (which is itself
	 * op-optimal: the crossed boundary M attains 0 at M and msk at M-1). So widen
	 * on carry MISMATCH (!=), not on any carry (the old ||). This subsumes the
	 * former constant special-case: equal corners => equal carries => never widened.
	 */
	if ((rv.u.min < rd->u.min) != (rv.u.max < rd->u.max))
		eval_umax_bound(&rv, msk);
#else
	if ((rd->u.min != rd->u.max || rs->u.min != rs->u.max) &&
			(rv.u.min < rd->u.min || rv.u.max < rd->u.max))
		eval_umax_bound(&rv, msk);
#endif

	/* uopt bridge 1: under the guard the sums did not wrap, so rv.u.{max,min}
	 * are >= rd->u.{max,min} and the widening test above is FALSE -- the corner
	 * sums survive the branch. */
	/*@ assert uopt_nowiden:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        (rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) &&
	         rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre)); */
#ifdef FIX_ADD_UNSIGNED_OVFL
	/* uopt bridge 1w, the BOTH-CARRY twin: min-corner carry implies max-corner
	 * carry (max sums dominate), both masked sums drop by exactly msk+1, the
	 * carry bits agree, the parity test above is FALSE, and the wrapped corner
	 * sums survive the branch. Linear form on purpose (no `&`). */
	/*@ assert uopt_nowiden_w:
	      \at(rd->u.min,Pre) + \at(rs->u.min,Pre) > msk ==>
	        (rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) - msk - 1 &&
	         rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre) - msk - 1); */
#endif

#if defined(FIX_ADD_SIGNED_OVFL_OPT)
	/*
	 * Optimal signed overflow handling: the two's-complement twin of the
	 * unsigned carry-parity test above. Each corner's wrap DIRECTION is a trit:
	 * underflow (addend < 0 yet the result ROSE) = -1, overflow (addend >= 0 yet
	 * the result FELL) = +1, otherwise 0. Because s.min <= s.max the min corner's
	 * trit is always <= the max corner's, so the three "equal" cases (0/0, +1/+1,
	 * -1/-1) are exactly the uniform wraps whose masked corner interval is the
	 * EXACT signed image; a mismatch is the only straddle of the signed seam,
	 * where [INT_MIN,INT_MAX] is op-optimal (both endpoints attained at the seam).
	 * So widen on direction MISMATCH. Supersedes the two branches below (it fixes
	 * the same negative-source over-widening AND the uniform-wrap over-widening);
	 * subsumes the constant special-case as the unsigned twin does.
	 */
	{
		int uf_min = (rs->s.min < 0 && rv.s.min > rd->s.min);
		int of_min = (rs->s.min >= 0 && rv.s.min < rd->s.min);
		int uf_max = (rs->s.max < 0 && rv.s.max > rd->s.max);
		int of_max = (rs->s.max >= 0 && rv.s.max < rd->s.max);
		if (uf_min != uf_max || of_min != of_max)
			eval_smax_bound(&rv, msk);
	}
#elif defined(FIX_ADD_SIGNED_OVFL)
	/*
	 * Precision (not soundness): the upstream signed-overflow guards have an
	 * UNGUARDED `rv.s.X < rd->s.X` term. When the source bound rs->s.X is
	 * negative the sum legitimately DECREASES (rv.s.X < rd->s.X) with no
	 * overflow, yet that term fires and widens the whole signed track to
	 * [INT_MIN, INT_MAX] — so adding any negative-ranged value throws away all
	 * signed precision. Guard each `<` term with `rs->s.X >= 0` (its true
	 * overflow direction: the min/max wraps DOWN only when the addend is
	 * non-negative; the addend-negative underflow wraps UP and is already the
	 * `rv.s.X > rd->s.X` term). Sound: when rs->s.X < 0 and rv.s.X < rd->s.X
	 * there is no wrap.
	 */
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.min < 0 && rv.s.min > rd->s.min) ||
			(rs->s.min >= 0 && rv.s.min < rd->s.min)) ||
			((rs->s.max < 0 && rv.s.max > rd->s.max) ||
				(rs->s.max >= 0 && rv.s.max < rd->s.max))))
		eval_smax_bound(&rv, msk);
#else
	if ((rd->s.min != rd->s.max || rs->s.min != rs->s.max) &&
			(((rs->s.min < 0 && rv.s.min > rd->s.min) ||
			rv.s.min < rd->s.min) ||
			((rs->s.max < 0 && rv.s.max > rd->s.max) ||
				rv.s.max < rd->s.max)))
		eval_smax_bound(&rv, msk);
#endif

	/*
	 * Split the ord goal: prove each half of range_ordering as its
	 * own (much smaller) obligation; the ensures then follows from
	 * store-forwarding alone.
	 */
	//@ assert ord_u: rv.u.min <= rv.u.max;
	//@ assert ord_s: rv.s.min <= rv.s.max;

	/* uopt FRAME step, split per endpoint. eval_smax_bound's assigns names only
	 * rv->s.{min,max}, so rv.u cannot have moved since uopt_nowiden -- but the
	 * conjunction (and the label-based \at form) both time out here, where the
	 * whole signed context is in scope. One endpoint at a time keeps each goal
	 * small enough to close. */
	/*@ assert uopt_sum_rv_max:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre); */
	/*@ assert uopt_sum_rv_min:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre); */
#ifdef FIX_ADD_UNSIGNED_OVFL
	/* Both-carry frame twins: the wrapped corner sums survive to the store. */
	/*@ assert uopt_sum_rv_max_w:
	      \at(rd->u.min,Pre) + \at(rs->u.min,Pre) > msk ==>
	        rv.u.max == \at(rd->u.max,Pre) + \at(rs->u.max,Pre) - msk - 1; */
	/*@ assert uopt_sum_rv_min_w:
	      \at(rd->u.min,Pre) + \at(rs->u.min,Pre) > msk ==>
	        rv.u.min == \at(rd->u.min,Pre) + \at(rs->u.min,Pre) - msk - 1; */
#endif

	/* sopt frame twins: under the no-signed-overflow guard the widening test
	 * above is FALSE, so eval_smax_bound did not fire and the corner sums
	 * established by sopt_nowrap_* survive to the store. */
	/*@ assert sopt_sum_rv_min:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre); */
	/*@ assert sopt_sum_rv_max:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre); */
#ifdef FIX_ADD_SIGNED_OVFL_OPT
	/* Uniform-wrap frame twins: under a both-overflow / both-underflow regime the
	 * trit-parity test is FALSE, eval_smax_bound does not fire, and the wrapped
	 * corner sums established by sopt_{of,uf}wrap_* survive to the store. */
	/*@ assert sopt_sum_rv_min_of:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_max_of:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) - msk - 1; */
	/*@ assert sopt_sum_rv_min_uf:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.min == \at(rd->s.min,Pre) + \at(rs->s.min,Pre) + msk + 1; */
	/*@ assert sopt_sum_rv_max_uf:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        rv.s.max == \at(rd->s.max,Pre) + \at(rs->s.max,Pre) + msk + 1; */
#endif

	rd->s = rv.s;
	rd->u = rv.u;

	/*
	 * uopt WITNESS, as a GROUND instance: self-optimality of each operand makes
	 * its own u endpoints representable (un_witness), so the corner PAIR is a
	 * bin_witness; combined with uopt_nowrap above, the corner sums ARE the
	 * stored endpoints. Stating it on concrete terms means the provers discharge
	 * the postcondition's existentials by instantiation instead of search.
	 */
	/* Split four ways: each conjunct is its own (much smaller) obligation. The
	 * two _wit_ goals are pure unfolding of self_optimal -> un_witness; the two
	 * _sum_ goals are uopt_nowrap plus store-forwarding. */
	/*@ assert uopt_wit_umax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.max,Pre), \at(rs->u.max,Pre), msk); */
	/*@ assert uopt_wit_umin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    \at(rd->u.min,Pre), \at(rs->u.min,Pre), msk); */
	/*@ assert uopt_sum_umax:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        ((\at(rd->u.max,Pre) + \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin:
	      \at(rd->u.max,Pre) + \at(rs->u.max,Pre) <= msk ==>
	        ((\at(rd->u.min,Pre) + \at(rs->u.min,Pre)) & msk) == rd->u.min; */
#ifdef FIX_ADD_UNSIGNED_OVFL
	/* Both-carry ground twins: the masked corner sum IS the stored endpoint.
	 * Discharged from uopt_sum_rv_*_w plus land_wrap_u32/u64 (each corner sum
	 * lies in (msk, 2*msk] under the hypothesis). */
	/*@ assert uopt_sum_umax_w:
	      \at(rd->u.min,Pre) + \at(rs->u.min,Pre) > msk ==>
	        ((\at(rd->u.max,Pre) + \at(rs->u.max,Pre)) & msk) == rd->u.max; */
	/*@ assert uopt_sum_umin_w:
	      \at(rd->u.min,Pre) + \at(rs->u.min,Pre) > msk ==>
	        ((\at(rd->u.min,Pre) + \at(rs->u.min,Pre)) & msk) == rd->u.min; */
#endif

	/* sopt WITNESS + sum, the signed twins. self_optimal supplies un_witness at
	 * the signed endpoints' PATTERNS (pat(v) == (uint64_t)v & msk), so those form
	 * the bin_witness; the _sum_ goals then say the pattern-sum reads back as the
	 * stored signed endpoint -- which is sopt_sum_rv_* plus store-forwarding. */
	/*@ assert sopt_wit_smax:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.max,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.max,Pre)) & msk, msk); */
	/*@ assert sopt_wit_smin:
	      self_optimal(\at(*rd,Pre), msk) && self_optimal(\at(*rs,Pre), msk) ==>
	        bin_witness(\at(*rd,Pre), \at(*rs,Pre),
	                    ((uint64_t)\at(rd->s.min,Pre)) & msk,
	                    ((uint64_t)\at(rs->s.min,Pre)) & msk, msk); */
	/*@ assert sopt_sum_smax:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin:
	      -(int64_t)(msk >> 1) - 1 <= \at(rd->s.min,Pre) + \at(rs->s.min,Pre) &&
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) <= (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
#ifdef FIX_ADD_SIGNED_OVFL_OPT
	/* Uniform-wrap ground twins. Both-overflow: all four signed bounds are
	 * POSITIVE (each min exceeds SMAX_w minus the other), so pattern == value,
	 * the pattern sum is the true sum in (msk>>1, msk], the outer & msk is the
	 * identity (land_id) and to_signed subtracts msk+1 -- matching
	 * sopt_sum_rv_*_of. Both-underflow: all four bounds NEGATIVE, patterns are
	 * value + msk+1, the pattern sum lands in (msk, 2*msk] where land_wrap
	 * subtracts msk+1, and to_signed is the identity on the small remainder --
	 * matching sopt_sum_rv_*_uf. */
	/*@ assert sopt_sum_smax_of:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin_of:
	      \at(rd->s.min,Pre) + \at(rs->s.min,Pre) > (int64_t)(msk >> 1) ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
	/*@ assert sopt_sum_smax_uf:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        to_signed(((((uint64_t)\at(rd->s.max,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.max,Pre)) & msk)) & msk, msk)
	          == rd->s.max; */
	/*@ assert sopt_sum_smin_uf:
	      \at(rd->s.max,Pre) + \at(rs->s.max,Pre) < -(int64_t)(msk >> 1) - 1 ==>
	        to_signed(((((uint64_t)\at(rd->s.min,Pre)) & msk) +
	                   (((uint64_t)\at(rs->s.min,Pre)) & msk)) & msk, msk)
	          == rd->s.min; */
#endif
}
