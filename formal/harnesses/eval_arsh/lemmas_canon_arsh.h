#ifndef LEMMAS_CANON_ARSH_H
#define LEMMAS_CANON_ARSH_H

#include "eval_arsh.h"

/*
 * FOLDED branch-soundness lemma (2026-07-28, dump-diagnosed; the
 * lsh/mul recipe). usound split part 04 — the 32-bit, u-track-negative
 * (od.u.min >= 2^31 pins every witness pattern into the negative half)
 * x s-track-straddling combination — carries BOTH shift branches' ite
 * stones, and the in-context search (unfold, skolemize, to_signed
 * case, asr_both_neg chain, wrap re-encode) dies at 1800s while the
 * other 96 parts prove. This lemma states that branch's unsigned
 * soundness against the folded predicate with bracket hypotheses
 * CHARACTER-FOR-CHARACTER in the stored term shapes
 * (land(msk32, to_uint64(lsr(to_sint32(endpoint), amount)))), so the
 * part closes by one instantiation whose hypotheses are the branch
 * conditions verbatim.
 *
 * A LEMMA, not an axiom — WP proves it in the driver's shift-opt
 * @lemma pass from the ArshShift family (axioms_arsh.h) plus
 * LandWrapTop (the negative re-encode: to_uint64(v) for v in
 * [-2^31,-1] lands in the top 2^32 block, so & msk32 is v + 2^32):
 * no new trust surface. Truth: all witness decodes sit in
 * [od.u.min - 2^32, od.u.max - 2^32] (within -2^31..-1), asr_both_neg
 * brackets every (decode >> y) by the two stored corners (crossed
 * amounts: min-corner shifts by os.u.min, max-corner by os.u.max),
 * and the +2^32 re-encode is monotone.
 *
 * TU-scoped ON PURPOSE, the lemmas_canon_lsh.h pattern: included from
 * eval_arsh.c only — NOT from eval_arsh.h, which the eval_alu TU also
 * includes (an extra quantified hypothesis there is a rule-14 hazard,
 * and axioms_arsh.h's header comment records the measured cost of
 * leaking arsh facts into other TUs).
 *
 * The bracket hypotheses are stated in the to_signed idiom the body's
 * own stones use (an (int32_t) cast in a logic term does not parse);
 * the usound_link_neg_* asserts in the all-negative branch restate the
 * stored endpoints in exactly this shape, so the discharge is
 * reflexive there.
 *
 * A COMPLETE per-branch family, not just the one red part: the first
 * neg32-only version closed part 04 and tipped margin-zero part 88
 * (the 32-bit all-non-negative combination) — a conclusion-triggered
 * lemma instantiates in EVERY usound part, and a part that has to
 * search after failing the wrong lemma's hypotheses loses margin. With
 * all four compute branches covered (neg/pos x 32/64), every
 * non-widening part discharges reflexively and stops depending on
 * search margin at all; the wrong-branch/wrong-mask attempts die on
 * one ground comparison (mask literal or the sign-half bound). The
 * pos lemmas' brackets are the BARE crossed lsr shapes the
 * non-negative branch stores (Qed strips the wrappers there);
 * lsr_both_anti (LenShift) carries their proof, asr_both_neg +
 * LandWrapTop the negative ones.
 */
/*@
lemma arsh_usound_neg32:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFF &&
	0x80000000 <= od.u.min && od.u.min <= od.u.max && od.u.max <= msk &&
	os.u.min <= os.u.max && os.u.max <= 31 &&
	nw.u.min == (((uint64_t)(to_signed(od.u.min, msk) >> os.u.min)) & msk) &&
	nw.u.max == (((uint64_t)(to_signed(od.u.max, msk) >> os.u.max)) & msk)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_neg64:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFFFFFFFFFF &&
	0x8000000000000000 <= od.u.min && od.u.min <= od.u.max &&
	os.u.min <= os.u.max && os.u.max <= 63 &&
	nw.u.min == (((uint64_t)(to_signed(od.u.min, msk) >> os.u.min)) & msk) &&
	nw.u.max == (((uint64_t)(to_signed(od.u.max, msk) >> os.u.max)) & msk)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_pos32:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFF &&
	od.u.min <= od.u.max && od.u.max <= (msk >> 1) &&
	os.u.min <= os.u.max && os.u.max <= 31 &&
	nw.u.min == (od.u.min >> os.u.max) &&
	nw.u.max == (od.u.max >> os.u.min)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);

lemma arsh_usound_pos64:
	\forall struct bpf_reg_val od, os, nw; \forall uint64_t msk;
	msk == 0xFFFFFFFFFFFFFFFF &&
	od.u.min <= od.u.max && od.u.max <= (msk >> 1) &&
	os.u.min <= os.u.max && os.u.max <= 63 &&
	nw.u.min == (od.u.min >> os.u.max) &&
	nw.u.max == (od.u.max >> os.u.min)
	==> eval_arsh_unsigned_soundness(od, os, nw, msk);
*/

#endif /* LEMMAS_CANON_ARSH_H */
