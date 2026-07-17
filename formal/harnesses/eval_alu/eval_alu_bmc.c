#include <assert.h>
#include "eval_alu.h"

uint64_t nondet_u64(void);
int64_t nondet_i64(void);
int nondet_int(void);
uint8_t nondet_u8(void);
int32_t nondet_i32(void);
int16_t nondet_i16(void);

#define REQUIRE(cond) do { if (!(cond)) return 0; } while (0)

/* ---- C mirrors of the ACSL predicates ---- */

static int is_scalar_or_pointer(enum rte_bpf_arg_type t)
{
	return t == RTE_BPF_ARG_RAW || t == RTE_BPF_ARG_PTR ||
		t == RTE_BPF_ARG_PTR_MBUF || t == RTE_BPF_ARG_RESERVED;
}

static int range_ordering(const struct bpf_reg_val *rv)
{
	return rv->u.min <= rv->u.max && rv->s.min <= rv->s.max;
}

static int range_within_width(const struct bpf_reg_val *rv, uint64_t mask)
{
	return rv->u.max <= mask &&
		-(int64_t)(mask >> 1) - 1 <= rv->s.min &&
		rv->s.max <= (int64_t)(mask >> 1);
}

/* canonical (sign-extended) reading of the low-w-bit pattern p */
static int64_t sext(uint64_t p, uint64_t m)
{
	return (p <= (m >> 1)) ? (int64_t)p : (int64_t)(p - (m + 1));
}

static void havoc_reg(struct bpf_reg_val *rv)
{
	rv->v.type = (enum rte_bpf_arg_type)nondet_int();
	rv->v.size = nondet_u64();
	rv->v.buf_size = nondet_u64();
	rv->mask = nondet_u64();
	rv->s.min = nondet_i64();
	rv->s.max = nondet_i64();
	rv->u.min = nondet_u64();
	rv->u.max = nondet_u64();
}

int main(void)
{
	struct bpf_eval_state st;
	struct bpf_verifier bvf;
	struct ebpf_insn ins;
	uint32_t i;

	bvf.evst = &st;

	for (i = 0; i != EBPF_REG_NUM; i++) {
		havoc_reg(&st.rv[i]);
		/* the verifier-loop register invariant (requires regs_ok) */
		REQUIRE(st.rv[i].v.type == RTE_BPF_ARG_UNDEF ||
			is_scalar_or_pointer(st.rv[i].v.type));
		REQUIRE(range_ordering(&st.rv[i]));
		REQUIRE(st.rv[i].mask == _32_BIT_MASK ||
			st.rv[i].mask == _64_BIT_MASK);
		REQUIRE(range_within_width(&st.rv[i], st.rv[i].mask));
	}

	ins.code = nondet_u8();
	ins.dst_reg = nondet_u8() & 0xf;
	ins.src_reg = nondet_u8() & 0xf;
	ins.off = nondet_i16();
	ins.imm = nondet_i32();

	/* upstream's ins_chk (WRT_REGS/RD_REGS masks) rejects register
	 * indices > 10 before eval_alu runs; the 4-bit fields alone reach 15 */
	REQUIRE(ins.dst_reg < EBPF_REG_NUM && ins.src_reg < EBPF_REG_NUM);

	REQUIRE(BPF_CLASS(ins.code) == BPF_ALU ||
		BPF_CLASS(ins.code) == EBPF_ALU64);

	uint32_t op = BPF_OP(ins.code);
#ifdef BMC_LIGHT_OPS
	/* keep the bit-vector queries linear: no multiply/divide/shifts */
	REQUIRE(op == BPF_ADD || op == BPF_SUB || op == BPF_AND ||
		op == BPF_OR || op == BPF_XOR || op == EBPF_MOV ||
		op == BPF_NEG);
#endif
#ifdef BMC_OP
	REQUIRE(op == (BMC_OP));
#endif
#ifdef BMC_32
	REQUIRE(BPF_CLASS(ins.code) == BPF_ALU);
#endif
#ifdef BMC_64
	REQUIRE(BPF_CLASS(ins.code) == EBPF_ALU64);
#endif

	uint64_t msk = (BPF_CLASS(ins.code) == BPF_ALU) ?
		_32_BIT_MASK : _64_BIT_MASK;

	/* pre state */
	const struct bpf_eval_state old = st;

	/* the definedness rejection, mirrored on the pre state */
	int selfxor = op == BPF_XOR && BPF_SRC(ins.code) == BPF_X &&
		ins.src_reg == ins.dst_reg;
	int undef =
		(op != EBPF_MOV && !selfxor &&
		 old.rv[ins.dst_reg].v.type == RTE_BPF_ARG_UNDEF) ||
		(op != BPF_NEG && BPF_SRC(ins.code) == BPF_X && !selfxor &&
		 old.rv[ins.src_reg].v.type == RTE_BPF_ARG_UNDEF);

#ifdef BMC_SND
	/*
	 * Value-soundness mirror (the usound/ssound ensures): pick a
	 * concrete operand pair the instruction could really operate on
	 * (an intersection witness of each referenced register, aliased
	 * when both operands name one register) and check afterwards that
	 * the tracked ranges cover the machine's true result. The witness
	 * registers additionally satisfy the mask/width part of the real
	 * verifier loop invariant, which every producer ensures.
	 */
	uint64_t wx = nondet_u64(), wy = nondet_u64();
	{
		const struct bpf_reg_val *wd = &old.rv[ins.dst_reg];
		const struct bpf_reg_val *ws = &old.rv[ins.src_reg];

		REQUIRE(wd->mask == _32_BIT_MASK || wd->mask == _64_BIT_MASK);
		REQUIRE(ws->mask == _32_BIT_MASK || ws->mask == _64_BIT_MASK);
		REQUIRE(range_within_width(wd, wd->mask));
		REQUIRE(range_within_width(ws, ws->mask));

		if (op != EBPF_MOV && !selfxor) {
			REQUIRE(wx <= wd->mask);
			REQUIRE(wd->u.min <= wx && wx <= wd->u.max);
			REQUIRE(wd->s.min <= sext(wx, wd->mask) &&
				sext(wx, wd->mask) <= wd->s.max);
		}
		if (BPF_SRC(ins.code) == BPF_X) {
			if (op != BPF_NEG) {
				REQUIRE(wy <= ws->mask);
				REQUIRE(ws->u.min <= wy && wy <= ws->u.max);
				REQUIRE(ws->s.min <= sext(wy, ws->mask) &&
					sext(wy, ws->mask) <= ws->s.max);
			}
			if (ins.src_reg == ins.dst_reg)
				REQUIRE(wy == wx);
		} else {
			wy = (uint64_t)ins.imm & msk;
		}
	}
#endif

	const char *err = eval_alu(&bvf, &ins);

	/* frame: only rv[dst_reg] may change */
	uint32_t j = nondet_u8();
	REQUIRE(j < EBPF_REG_NUM);
	if (j != ins.dst_reg) {
		assert(st.rv[j].v.type == old.rv[j].v.type &&
			st.rv[j].v.size == old.rv[j].v.size &&
			st.rv[j].v.buf_size == old.rv[j].v.buf_size &&
			st.rv[j].mask == old.rv[j].mask &&
			st.rv[j].s.min == old.rv[j].s.min &&
			st.rv[j].s.max == old.rv[j].s.max &&
			st.rv[j].u.min == old.rv[j].u.min &&
			st.rv[j].u.max == old.rv[j].u.max);     /* frame */
	}

	/* error semantics */
	assert(!undef || err != NULL);                          /* err_def */
	assert(err == NULL || undef ||
		op == BPF_DIV || op == BPF_MOD);                /* err_dom */
	assert(undef || op == BPF_DIV || op == BPF_MOD ||
		err == NULL);                                   /* noerr */

	/* the register invariant on the touched register, op width */
	if (err == NULL) {
		assert(is_scalar_or_pointer(st.rv[ins.dst_reg].v.type)); /* type_ok */
		assert(range_ordering(&st.rv[ins.dst_reg]));    /* uord + sord */
		assert(range_within_width(&st.rv[ins.dst_reg], msk)); /* uwidth + swidth */
	}

#ifdef BMC_SND
	if (err == NULL) {
		uint64_t px = wx & msk, py = wy & msk;
		uint64_t opbits = (msk == _32_BIT_MASK) ? 32 : 64;
		uint64_t pat = 0;
		int in_domain = 1;

		switch (op) {
		case BPF_ADD:  pat = (px + py) & msk; break;
		case BPF_SUB:  pat = (px - py) & msk; break;
		case BPF_MUL:  pat = (px * py) & msk; break;
		case BPF_DIV:
			if (py >= 1) pat = px / py; else in_domain = 0;
			break;
		case BPF_MOD:
			if (py >= 1) pat = px % py; else in_domain = 0;
			break;
		case BPF_AND:  pat = px & py; break;
		case BPF_OR:   pat = px | py; break;
		case BPF_XOR:  pat = px ^ py; break;
		case BPF_LSH:
			if (py < opbits) pat = (px << py) & msk;
			else in_domain = 0;
			break;
		case BPF_RSH:
			if (py < opbits) pat = px >> py;
			else in_domain = 0;
			break;
		case EBPF_ARSH:
			if (py < opbits)
				pat = (uint64_t)(sext(px, msk) >> py) & msk;
			else in_domain = 0;
			break;
		case BPF_NEG:  pat = (0 - px) & msk; break;
		case EBPF_MOV: pat = py; break;
		default:       in_domain = 0; break; /* fallback arm: full width */
		}

		if (in_domain) {
			assert(st.rv[ins.dst_reg].u.min <= pat &&
				pat <= st.rv[ins.dst_reg].u.max);        /* usound */
			assert(st.rv[ins.dst_reg].s.min <= sext(pat, msk) &&
				sext(pat, msk) <= st.rv[ins.dst_reg].s.max); /* ssound */
		}
	}
#endif

#ifdef BMC_SANITY
	/* must FAIL: proves the asserts above are reachable */
	assert(0);
#endif

	return 0;
}
