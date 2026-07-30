#ifndef LEMMAS_DELIVER_H
#define LEMMAS_DELIVER_H

#include "eval_alu.h"
#include "../eval_apply_mask/eval_apply_mask.h"
#include "../eval_and/eval_and.h"	/* to_signed_pattern_id */
#include "../eval_or/eval_or.h"
#include "../eval_xor/eval_xor.h"
#include "../../common/axioms_or.h"	/* lor bounds — .c-scoped upstream */
#include "../eval_xor/axioms_xor.h"	/* lxor bounds — .c-scoped upstream */
#include "../eval_add/eval_add.h"
#include "../eval_sub/eval_sub.h"
#include "../eval_mul/eval_mul.h"
#include "../eval_divmod/eval_divmod.h"
#include "../eval_neg/eval_neg.h"
#include "../eval_arsh/eval_arsh.h"
#include "../eval_lsh/eval_lsh.h"
#include "../eval_rsh/eval_rsh.h"

/*
 * PHASE C — the delivery layer for eval_alu's dispatcher-level value
 * soundness, plus the SIGNED composition lemmas proved 2026-07-29.
 *
 * Every lemma here is WP-PROVED (compose_deliver1.c 15/15,
 * compose_try_signed{7,8}.c). NOTHING in this header is an axiom: it
 * adds no trusted base. That matters because WP ASSUMES every in-scope
 * lemma — an unproved one here would silently fake the dispatcher proof
 * (observed on 2026-07-29: a compose lemma "proved" on top of four RED
 * strip lemmas, see compose_try_signed8.c). Read per-lemma results.
 *
 * The unsigned twins live in axioms_alu.h (12 lemmas, machine-proved).
 */

/*@
// ---- congruence bridge: encode-then-remask is the identity on the low
// w bits, per reachable (register mask, op mask) pair. Ground masks:
// with msk symbolic the land identities never fire.
lemma sext_remask_3232:
	\forall integer x; 0 <= x <= 0xFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFF)) & 0xFFFFFFFF) == (x & 0xFFFFFFFF);

lemma sext_remask_6464:
	\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFFFFFFFFFF)) & 0xFFFFFFFFFFFFFFFF)
		== (x & 0xFFFFFFFFFFFFFFFF);

lemma sext_remask_6432:
	\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==>
	(((uint64_t)to_signed(x, 0xFFFFFFFFFFFFFFFF)) & 0xFFFFFFFF)
		== (x & 0xFFFFFFFF);

// ---- THE DELIVERY LEMMA: per-track soundness of the masking step
// implies intersection-witness transport, which is exactly the
// hypothesis every composition lemma takes.
lemma wit_covers_from_apply_mask:
	\forall struct bpf_reg_val od, nw; \forall uint64_t msk;
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		(od.mask == 0xFFFFFFFF || od.mask == 0xFFFFFFFFFFFFFFFF) &&
		msk <= od.mask &&
		eval_apply_mask_unsigned_soundness(od, nw, msk) &&
		eval_apply_mask_signed_soundness(od, nw, msk)
		==> alu_wit_covers(od, nw, msk);

// ---- MOV: the arm the parked lemma set never covered. alu_dispatched
// includes EBPF_MOV and alu_op_pat returns the SOURCE value for it, so
// the dispatcher soundness predicate does constrain this arm. The result
// register simply IS the masked source (*rd = rs), so the transported
// source coverage — either alu_wit_covers for a register source or
// alu_imm_covers for an immediate, both bundled in alu_compose_pre — is
// already the whole statement.
lemma alu_compose_mov_u:
	\forall struct bpf_reg_val od, os, md, ms;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_MOV &&
		alu_compose_pre(od, os, md, ms, ins, msk)
		==> eval_alu_unsigned_soundness(od, os, ins, ms);

lemma alu_compose_mov_s:
	\forall struct bpf_reg_val od, os, md, ms;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_MOV &&
		alu_compose_pre(od, os, md, ms, ins, msk)
		==> eval_alu_signed_soundness(od, os, ins, ms);

// ---- CONGRUENCE of the transport predicates in their FIRST argument.
// alu_wit_covers / alu_imm_covers read only the five tracked fields, so
// two structs agreeing on those are interchangeable. In-code this turns
// "rewrite a quantified predicate's struct argument" — which the
// E-matcher will not do under the binder — into ONE instantiation with
// five ground field equalities as hypotheses. Same folded-lemma recipe
// as the operator soundness work.
lemma wit_covers_congr:
	\forall struct bpf_reg_val a, b, nw; \forall uint64_t msk;
		a.mask == b.mask &&
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_wit_covers(a, nw, msk)
		==> alu_wit_covers(b, nw, msk);

// Same, in the SECOND argument: relays restate a transport fact about a
// register whose fields have not changed since the stone was proved.
lemma wit_covers_congr2:
	\forall struct bpf_reg_val od, a, b; \forall uint64_t msk;
		a.mask == b.mask &&
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_wit_covers(od, a, msk)
		==> alu_wit_covers(od, b, msk);

lemma imm_covers_congr:
	\forall struct bpf_reg_val a, b; \forall struct ebpf_insn ins;
	\forall uint64_t msk;
		a.u.min == b.u.min && a.u.max == b.u.max &&
		a.s.min == b.s.min && a.s.max == b.s.max &&
		alu_imm_covers(a, ins, msk)
		==> alu_imm_covers(b, ins, msk);

// ---- or/xor strip lemmas: the two operators whose own predicate
// carries a trailing & msk that alu_op_pat does not.
lemma lor_strip_32:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
	==> ((a | b) & 0xFFFFFFFF) == (a | b);

lemma lor_strip_64:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
	==> ((a | b) & 0xFFFFFFFFFFFFFFFF) == (a | b);

lemma lxor_strip_32:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFF && 0 <= b <= 0xFFFFFFFF
	==> ((a ^ b) & 0xFFFFFFFF) == (a ^ b);

lemma lxor_strip_64:
	\forall integer a, b;
	0 <= a <= 0xFFFFFFFFFFFFFFFF && 0 <= b <= 0xFFFFFFFFFFFFFFFF
	==> ((a ^ b) & 0xFFFFFFFFFFFFFFFF) == (a ^ b);

// ---- SIGNED composition lemmas (the twins of axioms_alu.h), proved
// 2026-07-29. divmod/neg need no bridge (both tracks already over the
// same terms); and/add/sub/mul compose directly (their predicates cite
// the same SEM_* terms as alu_op_pat); or/xor need the strips above;
// arsh goes through to_signed_pattern_id.
lemma alu_compose_add_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_ADD &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_add_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_sub_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_SUB &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_sub_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_mul_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_MUL &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_mul_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_divmod_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		(BPF_OP(ins.code) == BPF_DIV ||
		 BPF_OP(ins.code) == BPF_MOD) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_divmod_signed_soundness(BPF_OP(ins.code), md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_and_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_AND &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_and_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_or_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_OR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_or_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_xor_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_XOR &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_xor_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_arsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == EBPF_ARSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_arsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_neg_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_NEG &&
		msk == alu_msk(ins.code) && !alu_selfxor(ins) &&
		alu_wit_covers(od, md, msk) &&
		eval_neg_signed_soundness(md, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_selfxor_s:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.s.min == 0 && nw.s.max == 0
		==> eval_alu_signed_soundness(od, os, ins, nw);

// ---- SELF-XOR, with the hypothesis actually available after dispatch.
// The variants above demand an exactly-[0,0] output, which eval_xor's
// contract does not promise (tightness is the PROVE_OPTIMALITY-gated
// uopt, not usound). But nothing stronger is needed: for the self-xor
// idiom alu_operands forces y == x, so the result pattern is x ^ x == 0
// for EVERY x — the destination range merely has to CONTAIN zero, which
// eval_xor's own usound/ssound give from the zeroed operands.
lemma alu_compose_selfxor_u_cover:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.u.min <= 0 <= nw.u.max
		==> eval_alu_unsigned_soundness(od, os, ins, nw);

lemma alu_compose_selfxor_s_cover:
	\forall struct bpf_reg_val od, os, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		alu_selfxor(ins) && msk == alu_msk(ins.code) &&
		nw.s.min <= 0 <= nw.s.max
		==> eval_alu_signed_soundness(od, os, ins, nw);

// (The xor_covers_zero_* lemmas were REMOVED 2026-07-29: only 1 of 4
// closed at 600s, and WP ASSUMES every in-scope lemma, so leaving
// three unproved ones here would have silently underwritten the
// dispatcher proof. Self-xor is an explicit exclusion in the
// contract instead -- see compose_deliver2.c.)

// ====================================================================
// SHIFT DISPATCH (lsh, rsh) -- added 2026-07-30, compose_try_signed12.c
// 33/33 and compose_try_signed13.c 28/28 (the latter with the shift
// axioms and canon headers REMOVED: this chain needs neither, so the
// header stays axiom-free).
//
// These two were the last signed composes to close, after six failed
// rounds of guessing at trigger shapes. What settled it was dumping the
// generated goal (-wp-out) and reading the terms, which showed THREE
// shapes where the approach had assumed two:
//
//   dispatcher (alu_op_pat):  land msk (lsl (land msk x) (land msk y))
//   operator   (eval_lsh):    land msk (lsl (land msk (to_uint64 i)) i1)
//   the r9/r10 bridge:        land msk (lsl i i1)         <-- a THIRD shape
//
// The bridge matched NEITHER side, so it manufactured two rewrites out
// of a problem that had one; and the strip lemma meant to close the gap
// could never fire, because the term it rewrites is only ever built
// inside the quantified hypothesis -- nothing ground to match.
//
// RULE: state an intermediate predicate in one of the two shapes it
// bridges, never in a third. Stated in the DISPATCHER's shape below,
// the compose step is a syntactic match and the adapter's only residual
// is cast_land_strip, whose LHS is exactly what instantiating the
// operator's forall at the already-masked value (x & msk) produces.
//
// The other ten operators need no bridge at all: their casts collapse
// under to_uint64 x == x once alu_witness gives is_uint64 x. Only the
// shift blocks that collapse (round 11: the direct form is the ONLY
// route that fails for lsh/rsh, red at 600s for both).

lemma cast_land_strip:
	\forall integer x; \forall uint64_t m;
	(m == 0xFFFFFFFF || m == 0xFFFFFFFFFFFFFFFF) && 0 <= x
	==> (((uint64_t)(x & m)) & m) == (x & m);

// The cast strip in the arrangement the adapter actually produces:
// applied to an already-masked base, nested under the shift.
lemma strip_cast_land_under_lsl_32:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) << q) & m) == ((((x & m)) << q) & m);

lemma strip_cast_land_under_lsl_64:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFFFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) << q) & m) == ((((x & m)) << q) & m);

lemma strip_cast_land_under_lsr_32:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) >> q)) == (((x & m)) >> q);

lemma strip_cast_land_under_lsr_64:
	\forall integer x, q; \forall uint64_t m;
	m == 0xFFFFFFFFFFFFFFFF && 0 <= x && 0 <= q
	==> (((((uint64_t)(x & m)) & m) >> q)) == (((x & m)) >> q);

// The bridge, in the dispatcher's shape.
predicate lsh_dpat_ssound(struct bpf_reg_val md, struct bpf_reg_val ms,
                          struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		0 <= x && 0 <= y &&
		un_witness(md, x & msk, msk) && un_witness(ms, y & msk, msk) &&
		(y & msk) < op_bits(msk)
			==> nw.s.min <= to_signed((((x & msk) << (y & msk)) & msk), msk)
			    <= nw.s.max;

predicate rsh_dpat_ssound(struct bpf_reg_val md, struct bpf_reg_val ms,
                          struct bpf_reg_val nw, uint64_t msk) =
	\forall integer x, y;
		0 <= x && 0 <= y &&
		un_witness(md, x & msk, msk) && un_witness(ms, y & msk, msk) &&
		(y & msk) < op_bits(msk)
			==> nw.s.min <= to_signed(((x & msk) >> (y & msk)), msk)
			    <= nw.s.max;

// step 1: operator predicate -> bridge
lemma lsh_dadapt:
	\forall struct bpf_reg_val md, ms, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	eval_lsh_signed_soundness(md, ms, nw, msk)
	==> lsh_dpat_ssound(md, ms, nw, msk);

lemma rsh_dadapt:
	\forall struct bpf_reg_val md, ms, nw; \forall uint64_t msk;
	(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
	eval_rsh_signed_soundness(md, ms, nw, msk)
	==> rsh_dpat_ssound(md, ms, nw, msk);

// step 2: bridge -> dispatcher
lemma alu_compose_lsh_s_dpat:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		lsh_dpat_ssound(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_rsh_s_dpat:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		rsh_dpat_ssound(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

// Fused: what the per-arm stones instantiate, ONE step like the other
// ten operators. NB this is nearly the statement that times out at 600s
// on its own (round 11 route A); it closes here only because the proved
// two-step bridge above is in scope for it.
lemma alu_compose_lsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_LSH &&
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_lsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);

lemma alu_compose_rsh_s:
	\forall struct bpf_reg_val od, os, md, ms, nw;
	\forall struct ebpf_insn ins; \forall uint64_t msk;
		BPF_OP(ins.code) == BPF_RSH &&
		(msk == 0xFFFFFFFF || msk == 0xFFFFFFFFFFFFFFFF) &&
		alu_compose_pre(od, os, md, ms, ins, msk) &&
		eval_rsh_signed_soundness(md, ms, nw, msk)
		==> eval_alu_signed_soundness(od, os, ins, nw);
*/

#endif /* LEMMAS_DELIVER_H */
