#ifndef AXIOMS_H
#define AXIOMS_H

#include "shared.h"

/*@
axiomatic LandMaskBound {
	axiom land_le_mask:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x & y) <= y;
	axiom land_id_u64:
		\forall integer x; 0 <= x <= 0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x;
	axiom land_id_u32:
		\forall integer x; 0 <= x <= 0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x;
}
*/

/*@
axiomatic BpfArgPtrType {
axiom ptr_flag_excludes_scalars:
	\forall integer t;
		(t & RTE_BPF_ARG_PTR) != 0 ==>
		t != RTE_BPF_ARG_UNDEF && t != RTE_BPF_ARG_RAW;
axiom no_ptr_flag_excludes_pointers:
	\forall integer t;
		(t & RTE_BPF_ARG_PTR) == 0 ==>
		t != RTE_BPF_ARG_PTR && t != RTE_BPF_ARG_PTR_MBUF &&
		t != RTE_BPF_ARG_RESERVED;
}
*/

//@ lemma land_comm: \forall integer x, y; (x & y) == (y & x);

/*@
axiomatic LandUint64AllOnes {
	axiom land_uint64_max:
	\forall integer x;
	0 <= x <= 0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x;
}

axiomatic LandUint32AllOnes {
	axiom land_uint32_max:
	\forall integer x;
	0 <= x <= 0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x;
}
*/

/*@
axiomatic LandBounds {
	axiom land_nonneg_le:
	\forall integer x, y;
	0 <= x && 0 <= y ==> 0 <= (x & y) <= x;
}
*/

/*@
axiomatic LandWrap {
	axiom land_wrap_u32:
		\forall integer x; 0xFFFFFFFF < x <= 2*0xFFFFFFFF ==> (x & 0xFFFFFFFF) == x - 0x100000000;
	axiom land_wrap_u64:
		\forall integer x;
		0xFFFFFFFFFFFFFFFF < x <= 2*0xFFFFFFFFFFFFFFFF ==> (x & 0xFFFFFFFFFFFFFFFF) == x - 0x10000000000000000;
}
*/

/*@
axiomatic LandWrapTop {
	axiom land_wrap_u32_top:
		\forall integer x;
		0xFFFFFFFF00000000 <= x <= 0xFFFFFFFFFFFFFFFF ==>
		(x & 0xFFFFFFFF) == x - 0xFFFFFFFF00000000;
}
*/

/*@
logic integer to_signed(integer v, integer msk) =
      v <= (msk >> 1) ? v : v - (msk + 1);

logic integer op_bits(integer msk) =
      msk == _32_BIT_MASK ? 32 : 64;
*/

/*@
axiomatic LenShift {
	axiom lsl_nonneg:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x << y);
	axiom lsl_val_mono:
		\forall integer a, b, y;
		0 <= a <= b && 0 <= y ==> (a << y) <= (b << y);
	axiom lsl_amt_mono:
		\forall integer x, p, q;
		0 <= x && 0 <= p <= q ==> (x << p) <= (x << q);
	axiom lsl_both_mono:
		\forall integer a, b, p, q;
		0 <= a <= b && 0 <= p <= q ==> (a << p) <= (b << q);
	axiom lsl_width_bound:
		\forall integer x, k, w;
		0 <= k <= w && 0 <= x && x <= (1 << (w - k)) - 1
		==> (x << k) <= (1 << w) - 1;
	axiom lsr_shrink:
		\forall integer x, y; 0 <= x && 0 <= y ==> 0 <= (x >> y) <= x;
	axiom lsr_val_mono:
		\forall integer a, b, y;
		0 <= a <= b && 0 <= y ==> (a >> y) <= (b >> y);
	axiom lsr_amt_anti:
		\forall integer x, p, q;
		0 <= x && 0 <= p <= q ==> (x >> q) <= (x >> p);
	axiom lsr_both_anti:
		\forall integer a, b, p, q;
		0 <= a <= b && 0 <= p <= q ==> (a >> q) <= (b >> p);
	axiom lsl_width_32:
		\forall integer x, k;
		0 <= k && k < 32 &&
		0 <= x && x <= (0xFFFFFFFFFFFFFFFF >> (64 - (32 - k)))
		==> (x << k) <= 0xFFFFFFFF;
	axiom lsl_width_64:
		\forall integer x, k;
		0 <= k && k < 64 &&
		0 <= x && x <= (0xFFFFFFFFFFFFFFFF >> (64 - (64 - k)))
		==> (x << k) <= 0xFFFFFFFFFFFFFFFF;
	axiom lsr_sign_any:
		\forall int64_t v; \forall integer w;
		31 <= w <= 63 && (((uint64_t)v) >> w) == 0 ==> 0 <= v;
	axiom lsr_allones_sint:
		\forall integer k;
		1 <= k <= 63
		==> 0 <= (0xFFFFFFFFFFFFFFFF >> k) <= 0x7FFFFFFFFFFFFFFF;
	axiom lsr_allones_33:
		\forall integer k;
		33 <= k <= 63
		==> (0xFFFFFFFFFFFFFFFF >> k) <= 0x7FFFFFFF;
	axiom lsl_swidth_32:
		\forall integer x, k;
		0 <= k && k <= 30 &&
		0 <= x && x < (0xFFFFFFFFFFFFFFFF >> (64 - (32 - k - 1)))
		==> (x << k) <= 0x7FFFFFFF;
	axiom lsl_swidth_64:
		\forall integer x, k;
		0 <= k && k <= 62 &&
		0 <= x && x < (0xFFFFFFFFFFFFFFFF >> (64 - (64 - k - 1)))
		==> (x << k) <= 0x7FFFFFFFFFFFFFFF;
}
*/

/*@
lemma lsr_half_32: (0xFFFFFFFF >> 1) == 0x7FFFFFFF;
lemma lsr_half_64: (0xFFFFFFFFFFFFFFFF >> 1) == 0x7FFFFFFFFFFFFFFF;

lemma len2mask_32: (0xFFFFFFFFFFFFFFFF >> 32) == 0xFFFFFFFF;
lemma len2mask_64: (0xFFFFFFFFFFFFFFFF >> 0) == 0xFFFFFFFFFFFFFFFF;

lemma op_bits_32: op_bits(0xFFFFFFFF) == 32;
lemma op_bits_64: op_bits(0xFFFFFFFFFFFFFFFF) == 64;

lemma shape_mask32: (0xFFFFFFFF & (0xFFFFFFFF + 1)) == 0;
lemma shape_mask64: (0xFFFFFFFFFFFFFFFF & (0xFFFFFFFFFFFFFFFF + 1)) == 0;
lemma shape_half32: (0x7FFFFFFF & (0x7FFFFFFF + 1)) == 0;
lemma shape_half64: (0x7FFFFFFFFFFFFFFF & (0x7FFFFFFFFFFFFFFF + 1)) == 0;
*/

#endif
