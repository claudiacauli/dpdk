/*
 * eval_alu — the ALU dispatcher. Verbatim body from
 * lib/bpf/bpf_validate.c; contract of record.
 *
 * Beyond the frame, error semantics and register-invariant clauses, this
 * file carries the DISPATCHER-LEVEL VALUE SOUNDNESS theorem (usound /
 * ssound): the composition of every per-operator soundness theorem
 * through the dispatch, on both tracks, for all 13 dispatched opcodes.
 * Merged from compose_deliver2.c on 2026-07-30 after it proved 43/43 in
 * one pass on a clean lemma base (lemmas_deliver.h 50/50 and
 * axioms_alu.h 26/26 standalone, ZERO new axioms).
 *
 * Two stated scope limits, different in kind — see the `width_fits`
 * note below, and docs/review_04_composition.md §4.
 *
 * WHEN RE-RUNNING THIS FILE: pass every operator .c file (as the
 * verify_all.sh cell does) and check that `missing-spec` appears ZERO
 * times. A spec-less run gives the operators default contracts, so the
 * per-arm stones prove nothing — and it can come out green.
 *
 * Delivery strategy (the 2026-07-16 attempt carried the UNFOLDED
 * quantified form across the heap and timed out at ~247s):
 *   - state each hypothesis as ONE FOLDED predicate (alu_wit_covers /
 *     alu_imm_covers) at the call site where the callee post is a single
 *     heap step away — atomic, so one e-matching instantiation;
 *   - discharge it from the PROVED delivery lemma
 *     wit_covers_from_apply_mask (compose_deliver1.c, 15/15) rather than
 *     from apply_mask's raw ensures;
 *   - relay across eval_defined, which `assigns \nothing`, so the facts
 *     survive without re-derivation.
 */
#include "eval_alu.h"
#include "../eval_defined/eval_defined.h"
#include "axioms_alu.h"			/* the 12 unsigned compose lemmas */
#include "lemmas_deliver.h"		/* delivery bridge + signed composes */
#include "../eval_apply_mask/eval_apply_mask.h"
#include "../eval_fill_imm/eval_fill_imm.h"
#include "../eval_add/eval_add.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_lsh/eval_lsh.h"
#include "../eval_rsh/eval_rsh.h"
#include "../eval_arsh/eval_arsh.h"
#include "../eval_and/eval_and.h"
#include "../eval_or/eval_or.h"
#include "../eval_xor/eval_xor.h"
#include "../eval_mul/eval_mul.h"
#include "../eval_divmod/eval_divmod.h"
#include "../eval_neg/eval_neg.h"
#include "../eval_max_bound/eval_max_bound.h"
/*
 * Dispatcher-level value soundness (usound/ssound) is PARKED, not stated
 * below. Its full architecture is proven-but-quarantined:
 *   - the folded predicates live in eval_alu.h (alu_op_pat, alu_witness,
 *     alu_compose_pre, eval_alu_{un,}signed_soundness);
 *   - the 12 UNSIGNED composition lemmas (all machine-proved in ~3s each,
 *     axioms_alu.h) and the 12 SIGNED twins (axioms_alu_signed.h, needing
 *     a per-operator low-bit congruence bridge) sit in headers that
 *     NOTHING INCLUDES — WP assumes every lemma in scope, so an unproven
 *     or unused-but-unfed lemma must not reach a live PO.
 * Why parked: the lemmas prove and apply (snd_add_u closes in 3s once fed
 * its hypotheses), but feeding them per dispatch arm needs a struct-value
 * bridged across the eval_defined call, and that heap plumbing times out
 * (es_add/pre_add, ~247s). See axioms_alu_signed.h for the diagnosis and
 * the order of work to finish it. The wsound witness-transport lemma on
 * eval_apply_mask and the mask/width strengthening of regs_ok below —
 * both proved — are the reusable half of this effort and are KEPT.
 */

/*@
	requires \valid(bvf) && \valid(bvf->evst) && \valid_read(ins);
	requires \valid(&bvf->evst->rv[0 .. EBPF_REG_NUM - 1]);
	requires \separated(bvf, bvf->evst, ins);
	requires \separated(&bvf->evst->rv[0 .. EBPF_REG_NUM - 1], ins);
	requires cls_ok: BPF_CLASS(ins->code) == BPF_ALU ||
		BPF_CLASS(ins->code) == EBPF_ALU64;
	// Upstream pre-validates register indices before eval_alu runs
	// (ins_chk's WRT_REGS/RD_REGS masks reject regs > 10); the 4-bit
	// bitfields alone would only bound them below 16. Stated as a
	// ground hypothesis both to make that upstream assumption explicit
	// and because WP models bitfield reads as masked loads whose range
	// the provers cannot recover — the regs_ok quantifier instantiates
	// at the two indices.
	requires idx_ok: 0 <= ins->dst_reg < EBPF_REG_NUM &&
		0 <= ins->src_reg < EBPF_REG_NUM;
	// The verifier-loop register invariant: every register is either
	// UNDEF or a scalar/pointer, both tracks are ordered, the tracked
	// mask is a supported width, and the ranges respect that width —
	// every producer establishes all of it (apply_mask's
	// mask_ok/uwidth/swidth, fill_imm's mask_set + width ensures, the
	// max_bound family); eval_alu's witness-transport chain
	// (apply_mask's wsound) consumes the mask and width facts.
	// OPERAND SCALARITY, the other half of the 2026-07-28 audit fix.
	// The operators require is_scalar of the registers they consume, and
	// that fact used to arrive from the (unsatisfiable) file-wide
	// is_scalar. Stated here at operand level instead: satisfiable in
	// real states (a scalar ALU op on scalar operands), and it makes the
	// SCOPE explicit -- ALU on POINTER operands (upstream eval_add's
	// pointer-arithmetic path, bpf_validate.c:665-674) is NOT covered by
	// this theorem. Verifying that path is separate work; see
	// docs/review_02_arg_audit.md finding 2.
	requires ops_scalar: is_scalar(bvf->evst->rv[ins->dst_reg].v.type) &&
		(BPF_SRC(ins->code) == BPF_X ==>
			is_scalar(bvf->evst->rv[ins->src_reg].v.type));
	// SCALAR-OR-POINTER, not is_scalar (2026-07-28 audit fix). The
	// previous file-wide is_scalar was UNSATISFIABLE in every reachable
	// state: the shipped validator installs R10 as the frame pointer
	// (bpf_validate.c:2933-2952, .v.type = BPF_ARG_PTR_STACK =
	// RTE_BPF_ARG_RESERVED), so no real program state ever had all 11
	// registers RAW and this whole contract was vacuous for real runs.
	// The two OPERAND registers still need is_scalar -- the operators
	// require it -- and that is established per-branch by the sc_d/sc_s
	// stones below from the ty_* type-provenance chain, not assumed
	// file-wide.
	requires regs_ok: \forall integer i; 0 <= i < EBPF_REG_NUM ==>
		is_scalar_or_pointer(bvf->evst->rv[i].v.type) &&
		range_ordering(&bvf->evst->rv[i]) &&
		(bvf->evst->rv[i].mask == _32_BIT_MASK ||
		 bvf->evst->rv[i].mask == _64_BIT_MASK) &&
		unsigned_range_within_width(&bvf->evst->rv[i],
			bvf->evst->rv[i].mask) &&
		signed_range_within_width(&bvf->evst->rv[i],
			bvf->evst->rv[i].mask);
	// SCOPE OF THE VALUE-SOUNDNESS ENSURES (Phase C, 2026-07-29).
	// usound/ssound below cover instructions whose OP WIDTH does not
	// exceed the width already tracked for the operands. The WIDENING
	// case — a register tracked at 32 bits read by a 64-bit ALU op — is
	// excluded, and NOT for proof-engineering reasons: eval_apply_mask
	// does not re-derive the signed track across a width increase
	// (smin64/smax64, eval_apply_mask.c:39-40, either KEEP the old bound
	// or top out). A register holding pattern 0x80000000 tracked at 32
	// bits has signed reading -2^31; its true 64-bit value is +2^31.
	// Keeping the old bound therefore describes the widened value
	// incorrectly, so alu_wit_covers is FALSE there and no amount of
	// search would prove it. This is the same cross-track consistency
	// gap FIX_APPLY_MASK_CONSIST names and never implemented (see the
	// deleted vld_d stone below). Tracked as a candidate defect; needs a
	// BMC witness before it is called one.
	requires width_fits:
		alu_msk(ins->code) <= bvf->evst->rv[ins->dst_reg].mask &&
		(BPF_SRC(ins->code) == BPF_X ==>
			alu_msk(ins->code) <= bvf->evst->rv[ins->src_reg].mask);
	terminates \true;
	// Framing: ONLY the destination register may change — certified by
	// this assigns clause (checked as its own side-goal); an explicit
	// quantified struct-equality ensures re-derives the same fact the
	// hard way and times out in this TU.
	assigns bvf->evst->rv[ins->dst_reg];

	// Error semantics: the definedness rejection is exact on the pre
	// state; any other error can only come from the div/mod
	// constant-zero-divisor rejection.
	ensures err_def: alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type))
		==> \result != \null;
	ensures err_dom: \result != \null ==>
		alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type)) ||
		BPF_OP(ins->code) == BPF_DIV || BPF_OP(ins->code) == BPF_MOD;
	ensures noerr: !alu_undef(*ins,
			\old(bvf->evst->rv[ins->dst_reg].v.type),
			\old(bvf->evst->rv[ins->src_reg].v.type)) &&
		BPF_OP(ins->code) != BPF_DIV && BPF_OP(ins->code) != BPF_MOD
		==> \result == \null;
	// The register invariant is re-established on the touched register
	// for the op width whenever the instruction is accepted.
	ensures type_ok: \result == \null ==>
		is_scalar(bvf->evst->rv[ins->dst_reg].v.type);
	ensures uord: \result == \null ==>
		unsigned_range_ordering(&bvf->evst->rv[ins->dst_reg]);
	ensures sord: \result == \null ==>
		signed_range_ordering(&bvf->evst->rv[ins->dst_reg]);
	ensures uwidth: \result == \null ==>
		unsigned_range_within_width(&bvf->evst->rv[ins->dst_reg],
			alu_msk(ins->code));
	ensures swidth: \result == \null ==>
		signed_range_within_width(&bvf->evst->rv[ins->dst_reg],
			alu_msk(ins->code));
	// DISPATCHER-LEVEL VALUE SOUNDNESS (Phase C, 2026-07-29): whatever
	// concrete values the referenced registers could really hold before
	// the instruction, the machine's true result for this operation lies
	// within the ranges tracked afterwards. This is the composition of
	// every per-operator soundness theorem through the dispatch, and it
	// is what makes "the validator never accepts a program whose ALU
	// result escapes its tracked ranges" a single stated theorem.
	ensures usound: \result == \null && !alu_selfxor(*ins) ==>
		eval_alu_unsigned_soundness(
			\old(bvf->evst->rv[ins->dst_reg]),
			\old(bvf->evst->rv[ins->src_reg]),
			*ins, bvf->evst->rv[ins->dst_reg]);
	// SIGNED track, every dispatched operator — no opcode exclusion.
	// LSH/RSH were the last two to close (2026-07-30, round 12): the
	// fix was to state the bridging predicate in the DISPATCHER's term
	// shape rather than in a third shape of its own, after a -wp-out
	// dump showed the r9/r10 bridge matched neither side it bridged.
	// See lemmas_deliver.h and docs/review_04_composition.md §4.3.
	ensures ssound: \result == \null && !alu_selfxor(*ins) ==>
		eval_alu_signed_soundness(
			\old(bvf->evst->rv[ins->dst_reg]),
			\old(bvf->evst->rv[ins->src_reg]),
			*ins, bvf->evst->rv[ins->dst_reg]);
	// OP-OPTIMALITY: per-branch -- eval_alu only DISPATCHES to the per-op eval_*
	// functions, so op-optimality (and its self-optimality precondition) is exactly
	// that of the branch taken; nothing to state at the dispatcher level.
	// optimality_notes.md §6h.
*/
const char *
eval_alu(struct bpf_verifier *bvf, const struct ebpf_insn *ins)
{
	uint64_t msk;
	uint32_t op;
	size_t opsz, sz;
	const char *err;
	struct bpf_eval_state *st;
	struct bpf_reg_val *rd, rs;

	sz = (BPF_CLASS(ins->code) == BPF_ALU) ?
		sizeof(uint32_t) : sizeof(uint64_t);
	opsz = sz * CHAR_BIT;
	msk = RTE_LEN2MASK(opsz, uint64_t);

	st = bvf->evst;
	rd = st->rv + ins->dst_reg;

	/*
	 * Instantiate the regs_ok invariant at the two referenced registers
	 * HERE, in the pristine pre-mutation context (the eval_mul ob32 /
	 * msk_shape pattern): the quantifier fires cheaply and the ensures
	 * consume these ground facts instead of hunting the instantiation
	 * inside the post-dispatch POs, where the 22-file axiom set drowns
	 * the E-matcher.
	 */
	/*@ assert inv_d: is_scalar(rd->v.type); */
	/* CONDITIONAL since the 2026-07-28 audit fix: source scalarity is
	 * required (and needed) only for a REGISTER source. For BPF_K the
	 * src field is unused -- ins_chk pins it to ZERO_REG and rs is
	 * materialised by fill_imm as RAW -- so nothing downstream reads
	 * the src register's type on that path (ty_s is likewise
	 * X-guarded). */
	/*@ assert inv_s: BPF_SRC(ins->code) == BPF_X ==>
	      is_scalar(st->rv[ins->src_reg].v.type); */
	/*@ assert ord_d: range_ordering(rd); */
	/*@ assert ord_s: range_ordering(&st->rv[ins->src_reg]); */

	if (BPF_SRC(ins->code) == BPF_X) {
		rs = st->rv[ins->src_reg];
		eval_apply_mask(&rs, msk);
		/* DELIVERY (source, register operand). apply_mask's usound/ssound
		 * are one heap step away here; wit_covers_from_apply_mask folds
		 * them into the single atomic predicate the composition lemmas
		 * take as a hypothesis. Stating it HERE and not after the merge
		 * is the whole point: the callee post is still in reach. */
		/*@ assert wc_s: alu_wit_covers(
		      \at(bvf->evst->rv[ins->src_reg], Pre), rs, msk); */
		/* relay ord_d across THIS arm's rs-local call: asserted here
		 * (one callee post, unmerged heap) because after the branch
		 * merge the same fact does not close even at 900s.
		 * SPLIT per track (2026-07-28): the whole-predicate stones went
		 * margin-zero as the operator contracts grew -- ord_dk red in
		 * three consecutive isolated 1200s runs, ord_dx oscillating at
		 * ~half ceiling -- with every candidate culprit exonerated
		 * individually (METHOD rule 13: fix structurally). Half the
		 * conclusion, same relay point. */
		/*@ assert ord_dx_u: unsigned_range_ordering(rd); */
		/*@ assert ord_dx_s: signed_range_ordering(rd); */
	} else {
		rs = (struct bpf_reg_val){.v = {.size = sz,},};
		eval_fill_imm(&rs, msk, ins->imm);
		/* DELIVERY (source, immediate operand): fill_imm's const_u/const_s
		 * pin both tracks to the materialised immediate exactly, which is
		 * the K-source half of alu_compose_pre. */
		/*@ assert ic_s: alu_imm_covers(rs, *ins, msk); */
		/*@ assert ord_dk_u: unsigned_range_ordering(rd); */
		/*@ assert ord_dk_s: signed_range_ordering(rd); */
	}

	/* DELIVERY (destination), SPLIT via a C label (2026-07-29). The
	 * single-stone form timed out at 900s while its source-side twin
	 * proved in 494ms: the difference is that rd is a HEAP pointer, so
	 * one goal had to both apply the delivery lemma AND relate *rd back
	 * to Pre through the branch merge. Splitting gives each half a
	 * ground fact: pin_d is a plain struct equality over an untouched
	 * location (nothing above writes the heap — the branch arms write
	 * only the local rs), and wc_d then applies the lemma entirely in
	 * terms of the label, where apply_mask's post is one step away. */
	PreMask: eval_apply_mask(rd, msk);

	/* wc_d applies the delivery lemma in LABEL-RELATIVE terms and proves
	 * in ~2s. Connecting the label back to Pre is separate bookkeeping —
	 * and the whole-STRUCT equality for it times out (the same fact the
	 * certified file notes "re-derives the same fact the hard way and
	 * times out in this TU"). So pin the FIVE FIELDS alu_wit_covers
	 * actually reads, as scalar equalities: each is a single untouched
	 * heap location, and the folded predicate then rewrites field-wise.
	 * Ground-pin pattern, cf. sx_rs_zero. */
	/*@ assert wc_d: alu_wit_covers(\at(*rd, PreMask), *rd, msk); */
	/*@ assert pin_d_mask: \at(rd->mask, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].mask, Pre); */
	/*@ assert pin_d_umin: \at(rd->u.min, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].u.min, Pre); */
	/*@ assert pin_d_umax: \at(rd->u.max, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].u.max, Pre); */
	/*@ assert pin_d_smin: \at(rd->s.min, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].s.min, Pre); */
	/*@ assert pin_d_smax: \at(rd->s.max, PreMask) ==
	      \at(bvf->evst->rv[ins->dst_reg].s.max, Pre); */
	/* Now the Pre-form, which is what the usound/ssound ensures need. */
	/*@ assert wc_d_pre: alu_wit_covers(
	      \at(bvf->evst->rv[ins->dst_reg], Pre), *rd, msk); */

	/*
	 * Type-provenance stones: apply_mask's unchanged_v keeps both
	 * operand types (fill_imm materialises RAW); pinning them HERE, one
	 * heap step from Pre, hands the err/type ensures a linear chain
	 * instead of a heap-update hunt through the whole dispatch.
	 */
	/*@ assert ty_d: rd->v.type ==
	      \at(bvf->evst->rv[ins->dst_reg].v.type, Pre); */
	/*@ assert ty_s: BPF_SRC(ins->code) == BPF_X ==>
	      rs.v.type == \at(bvf->evst->rv[ins->src_reg].v.type, Pre); */
	/*@ assert ty_k: BPF_SRC(ins->code) != BPF_X ==>
	      rs.v.type == RTE_BPF_ARG_RAW; */

	op = BPF_OP(ins->code);

	/* Allow self-xor as way to zero register */
	if (op == BPF_XOR && BPF_SRC(ins->code) == BPF_X &&
	    ins->src_reg == ins->dst_reg) {
		eval_fill_imm(&rs, UINT64_MAX, 0);
		eval_fill_imm(rd, UINT64_MAX, 0);
		/*@ assert ty_sx: rd->v.type == RTE_BPF_ARG_RAW &&
		      rs.v.type == RTE_BPF_ARG_RAW; */
		/* ground zero-pins (2026-07-28): rs carries THREE layered callee
		 * posts by here (arm init + arm call + this zeroing) and its
		 * split validity stone still spun; pin the four zeroed fields as
		 * ground values (fill_imm's const_u/const_s at imm 0) so the
		 * vld/wid stones below unfold on literals, not post chains. */
		/*@ assert sx_rs_zero: rs.u.min == 0 && rs.u.max == 0 &&
		      rs.s.min == 0 && rs.s.max == 0; */
		/*@ assert sx_rd_zero: rd->u.min == 0 && rd->u.max == 0 &&
		      rd->s.min == 0 && rd->s.max == 0; */
		/* the zeroed registers are trivially well-formed at ANY op
		 * width; pinned here (tiny context) because fill_imm's
		 * ensures speak of UINT64_MAX while the operators need msk.
		 * PER-MASK: with msk symbolic the msk>>1 terms inside
		 * range_validity never ground (the standard per-mask
		 * conditional-stone pattern, cf. eval_mul's u_nof32/64). */
		/* per-REGISTER split (2026-07-28), same rationale as ord_dx_*:
		 * the two-register conjunction sat at margin zero. */
		/*@ assert sx_vld32_rs: msk == _32_BIT_MASK ==>
		      range_validity(&rs, msk); */
		/*@ assert sx_vld32_rd: msk == _32_BIT_MASK ==>
		      range_validity(rd, msk); */
		/*@ assert sx_vld64_rs: msk == _64_BIT_MASK ==>
		      range_validity(&rs, msk); */
		/*@ assert sx_vld64_rd: msk == _64_BIT_MASK ==>
		      range_validity(rd, msk); */
		/*@ assert sx_wid32: msk == _32_BIT_MASK ==>
		      range_within_width(&rs, msk) &&
		      range_within_width(rd, msk); */
		/*@ assert sx_wid64: msk == _64_BIT_MASK ==>
		      range_within_width(&rs, msk) &&
		      range_within_width(rd, msk); */
	}

	err = eval_defined((op != EBPF_MOV) ? rd : NULL,
			   (op != BPF_NEG) ? &rs : NULL);
	if (err != NULL)
		return err;

	/*
	 * Operand-wellformedness stones: every operator requires
	 * range_ORDERING + range_within_width of both operands at msk (NOT
	 * validity -- the intersection-soundness refactor dropped agreement
	 * from every operator's precondition). apply_mask's and fill_imm's
	 * ensures give them; asserting them HERE hands each requires-instance
	 * a ground fact instead of a re-derivation inside the giant
	 * post-dispatch POs.
	 *
	 * `vld_d: range_validity(rd, msk)` USED to sit here and is DELETED
	 * (2026-07-19). It was FALSE at this point and had never proved:
	 * eval_apply_mask does not re-establish AGREEMENT across a width
	 * change, and the FIX_APPLY_MASK_CONSIST repair the old comment
	 * appealed to was never implemented (defined in common/fixes.h, no
	 * #ifdef anywhere). Its only consumer was eval_neg, whose
	 * range_validity precondition has been relaxed to range_ordering now
	 * that FIX_NEG_CROSS_INVERT guards the cross-track clamps directly.
	 * BMC grid: harnesses/eval_neg/eval_neg_pre_bmc.c.
	 */
	/*@ assert ord_d2: range_ordering(rd); */
	/*@ assert wid_d: range_within_width(rd, msk); */
	// scalar-scope: hand each operator's is_scalar(...) requires-instance a
	// ground fact (from inv_d/inv_s via the ty_* type-provenance stones).
	/*@ assert sc_d: is_scalar(rd->v.type); */
	/*@ assert sc_s: is_scalar(rs.v.type); */
	/*
	 * `vld_s32` / `vld_s64` (range_validity of the SOURCE operand) were
	 * DELETED here (2026-07-19), for the same reason as vld_d above: both
	 * were FALSE and neither had ever proved. No operator requires
	 * range_validity any more -- the intersection-soundness refactor
	 * dropped it everywhere, and eval_neg (the last holdout) is unary, so
	 * it never even sees `rs`. Source ordering comes from ord_s below.
	 */
	/*@ assert ord_s2: range_ordering(&rs); */

	/* SEPARATION + FIELD PINS for the source relay. `rs` is a LOCAL but
	 * it is ADDRESS-TAKEN (eval_apply_mask(&rs, ...)), so WP models it in
	 * the heap and cannot, on its own, rule out that eval_apply_mask(rd,
	 * msk) aliased it — which is why the wc_s2/ic_s2 relays failed while
	 * their in-branch originals proved. State the separation, then pin
	 * the four tracked fields across the intervening calls so the
	 * congruence lemmas can move the predicate onto the current value.
	 * (The \separated fact is the one the typed memory model needs;
	 * without it, post-store reads of rs are falsifiable.) */
	/*@ assert sep_rs: \separated(&rs, rd); */
	/*@ assert sep_rs_evst: \separated(&rs, &bvf->evst->rv[0 ..
	      EBPF_REG_NUM - 1]); */

	/* DELIVERY RELAY across eval_defined (which `assigns \nothing`, so
	 * nothing above can have changed) and past the self-xor rewrite.
	 * Re-stated HERE, in the state the dispatch POs are evaluated in, so
	 * each composition lemma finds its hypothesis as a ground fact rather
	 * than re-deriving it through the branch merge. Self-xor is excluded:
	 * that path zeroes both registers and is discharged by the dedicated
	 * alu_compose_selfxor_{u,s} lemmas from the zero pins. */
	/*@ assert wc_d2: !alu_selfxor(*ins) ==> alu_wit_covers(
	      \at(bvf->evst->rv[ins->dst_reg], Pre), *rd, msk); */
	/*@ assert wc_s2: !alu_selfxor(*ins) && BPF_SRC(ins->code) == BPF_X ==>
	      alu_wit_covers(\at(bvf->evst->rv[ins->src_reg], Pre), rs, msk); */
	/*@ assert ic_s2: BPF_SRC(ins->code) != BPF_X ==>
	      alu_imm_covers(rs, *ins, msk); */
	/* The shared hypothesis bundle every composition lemma takes, folded
	 * into ONE predicate — this is the fact the 2026-07-16 attempt tried
	 * to carry unfolded. */
	/*@ assert cpre: !alu_selfxor(*ins) && msk == alu_msk(ins->code) ==>
	      alu_compose_pre(\at(bvf->evst->rv[ins->dst_reg], Pre),
	                      \at(bvf->evst->rv[ins->src_reg], Pre),
	                      *rd, rs, *ins, msk); */
	/*@ assert wid_s32: msk == _32_BIT_MASK ==>
	      range_within_width(&rs, msk); */
	/*@ assert wid_s64: msk == _64_BIT_MASK ==>
	      range_within_width(&rs, msk); */


	/*
	 * PER-ARM SOUNDNESS STONES (Phase C, 2026-07-29). Monolithic, the
	 * usound ensures times out at 1800s; under -wp-split it becomes 960
	 * parts of which 17 straggle (clustered, i.e. specific arms). Each
	 * stone below turns its arm into ONE composition-lemma instantiation
	 * in a small context: the lemma's hypotheses are exactly `cpre` (a
	 * ground fact by here) plus the operator's own usound/ssound
	 * postcondition, one heap step away. The ensures then follows from
	 * the arm disjunction instead of being re-derived per split part.
	 * Same per-branch-relay shape as the dispatcher's ord_dx/ord_dk
	 * stones. selfxor is excluded here and carried by its own lemma from
	 * the zero pins; the `else` arm widens to full width, where
	 * alu_dispatched is false and the predicate is vacuous.
	 */
	if (op == BPF_ADD) {
		eval_add(rd, &rs, msk);
		/*@ assert us_add: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_add: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_SUB) {
		eval_sub(rd, &rs, msk);
		/*@ assert us_sub: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_sub: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_LSH) {
		eval_lsh(rd, &rs, opsz, msk);
		/*@ assert us_lsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_lsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_RSH) {
		eval_rsh(rd, &rs, opsz, msk);
		/*@ assert us_rsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_rsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == EBPF_ARSH) {
		eval_arsh(rd, &rs, opsz, msk);
		/*@ assert us_arsh: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_arsh: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_AND) {
		eval_and(rd, &rs, opsz, msk);
		/*@ assert us_and: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_and: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_OR) {
		eval_or(rd, &rs, opsz, msk);
		/*@ assert us_or: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_or: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_XOR) {
		eval_xor(rd, &rs, opsz, msk);
		/* selfxor took the zeroing path above and is covered by
		 * alu_compose_selfxor_{u,s} from the zero pins. */
		/*@ assert us_xor: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_xor: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/* SELF-XOR is EXCLUDED from the value-soundness ensures
		 * (see the contract note). Its soundness is TRUE and easy
		 * to see by hand -- alu_operands forces y == x, so the
		 * result is x ^ x == 0, and eval_xor is sound so its output
		 * range must contain 0 -- but mechanising it needs
		 * eval_xor's soundness INSTANTIATED at the witness pair
		 * (0,0), i.e. a witness guess inside a quantified
		 * hypothesis. Measured 2026-07-29: the in-code stones time
		 * out at 900s and only 1 of 4 folded ground-mask lemmas
		 * (xor_covers_zero_*) closes at 600s. Left as an explicit
		 * exclusion rather than an assumed assert. */
	} else if (op == BPF_MUL) {
		eval_mul(rd, &rs, opsz, msk);
		/*@ assert us_mul: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_mul: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_DIV || op == BPF_MOD) {
		err = eval_divmod(op, rd, &rs, msk);
		/*@ assert us_divmod: !alu_selfxor(*ins) && err == \null ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_divmod: !alu_selfxor(*ins) && err == \null ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == BPF_NEG) {
		eval_neg(rd, opsz, msk);
		/*@ assert us_neg: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_neg: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else if (op == EBPF_MOV) {
		*rd = rs;
		/*@ assert us_mov: !alu_selfxor(*ins) ==>
		      eval_alu_unsigned_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
		/*@ assert ss_mov: !alu_selfxor(*ins) ==>
		      eval_alu_signed_soundness(
		        \at(bvf->evst->rv[ins->dst_reg], Pre),
		        \at(bvf->evst->rv[ins->src_reg], Pre), *ins, *rd); */
	} else {
		eval_max_bound(rd, msk);
		/* alu_dispatched(op) is FALSE here, so both soundness
		 * predicates hold vacuously — no stone needed. */
	}

	/*
	 * MERGE STONES. The per-arm stones above are branch postconditions;
	 * at this point WP holds their disjunction. Collapsing that to one
	 * fact HERE makes the remaining step PROPOSITIONAL (pick the arm,
	 * quote its stone) instead of leaving the ensures to redo the case
	 * analysis with all the arithmetic in scope — which times out at
	 * 1800s monolithic and leaves 17 straggler parts under -wp-split.
	 */
	/* Stated on bvf->evst->rv[ins->dst_reg], NOT on *rd: the ensures
	 * re-reads the register through that access path, and making the
	 * stone syntactically match saves the final goal from also having to
	 * re-derive rd == &bvf->evst->rv[ins->dst_reg] with the whole
	 * dispatch context in scope. No selfxor guard here — the self-xor
	 * arm now has its own stones. */
	/*@ assert us_all: !alu_selfxor(*ins) && err == \null ==>
	      eval_alu_unsigned_soundness(
	        \at(bvf->evst->rv[ins->dst_reg], Pre),
	        \at(bvf->evst->rv[ins->src_reg], Pre), *ins,
	        bvf->evst->rv[ins->dst_reg]); */
	/* SIGNED: no opcode exclusion — LSH/RSH closed 2026-07-30
	 * (compose_try_signed12.c 33/33, lemmas_deliver.h 50/50 standalone),
	 * so the signed track now covers every dispatched operator. */
	/*@ assert ss_all: !alu_selfxor(*ins) && err == \null ==>
	      eval_alu_signed_soundness(
	        \at(bvf->evst->rv[ins->dst_reg], Pre),
	        \at(bvf->evst->rv[ins->src_reg], Pre), *ins,
	        bvf->evst->rv[ins->dst_reg]); */

	return err;
}
