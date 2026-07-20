#include "eval_fill_imm64.h"

#ifdef FIX_FILL_IMM_SIGNED_32
/*
 * Sign-extend the low-w-bit pattern p (in [0, mask]) to its canonical
 * signed value — the C computation of to_signed(p, mask). Same helper
 * as eval_mul's mul_sext / eval_divmod's dm_sext / eval_neg's neg_sext.
 */
/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires 0 <= p <= mask;
	assigns \nothing;
	ensures \result == to_signed(p, mask);
*/
static int64_t fi_sext(uint64_t p, uint64_t mask)
{
	return (p <= (mask >> 1)) ? (int64_t)p : (int64_t)(p - (mask + 1));
}
#endif

/*@
	requires mask == _32_BIT_MASK || mask == _64_BIT_MASK;
	requires 0 <= val <= mask;
	requires \valid(rv);
	terminates \true;
	assigns rv->mask, rv->s, rv->u;

	ensures mask_set:   rv->mask == mask;
	ensures const_u:    rv->u.min == val && rv->u.max == val;
	ensures const_s:    rv->s.min == to_signed(val, mask) &&
			rv->s.max == rv->s.min;
	ensures uord:       unsigned_range_ordering(rv);
	ensures sord:       signed_range_ordering(rv);
	ensures uwidth:     unsigned_range_within_width(rv, mask);
	ensures swidth:     signed_range_within_width(rv, mask);

	// SELF-OPTIMALITY: TRIVIAL (Category C) but stated as a first-class clause
	// anyway. const_u/const_s pin a SINGLE-POINT register, so all four range
	// endpoints are the same one value and each is trivially attained by it.
	// There is no OP-optimality clause because there is no input register to be
	// optimal WITH RESPECT TO -- this is a nullary transformer, so output
	// self-optimality is the whole content of "optimal" here.
	//
	// Worth having as a real goal rather than a comment: this is the FREE BASE
	// CASE for any future self-optimality-PRESERVATION invariant
	// (optimality_notes.md §6i, §7 #2) -- the induction has to start somewhere,
	// and this is the somewhere.
	ensures selfopt:    self_optimal(*rv, mask);
*/
void
eval_fill_imm64(struct bpf_reg_val *rv, uint64_t mask, uint64_t val)
{
	rv->mask = mask;
#ifdef FIX_FILL_IMM_SIGNED_32
	/*
	 * Upstream stores the w-bit PATTERN val in s.min/s.max. For the
	 * 64-bit mask the int64 store reinterprets it correctly (a negative
	 * imm sign-extends through (uint64_t)imm & mask and wraps back),
	 * but for msk == 2^32-1 a negative imm leaves a large POSITIVE
	 * pattern in the signed track: eval_fill_imm(msk32, -1) tracks
	 * s = [0xFFFFFFFF, 0xFFFFFFFF] while the canonical reading of the
	 * register is -1. Every 32-bit BPF_K instruction takes this rs, so
	 * the signed track of AND/OR/... with a negative immediate is
	 * corrupted at the source. Store the canonical (sign-extended)
	 * reading instead; identity for the 64-bit mask.
	 *
	 * Violates (unfixed): swidth and const_s (0xFFFFFFFF > INT32_MAX;
	 * the tracked signed constant is not the register's canonical
	 * reading) — ESBMC witness on eval_fill_imm_bmc.c (BMC_32,
	 * negative imm); the 64-bit mask is unaffected.
	 */
	rv->s.min = fi_sext(val, mask);
	rv->s.max = rv->s.min;
#else
	rv->s.min = val;
	rv->s.max = val;
#endif
	rv->u.min = val;
	rv->u.max = val;
}
