/*
 * tests.c — runtime playground for the DPDK BPF validator range tracking
 * ======================================================================
 *
 * This compiles and RUNS the real eval_alu dispatcher and the operator
 * evaluators as ordinary C. The ACSL annotations (the Frama-C proof
 * comments) scattered through those files are just comments to a C
 * compiler, so the behaviour you observe here is exactly the production
 * range-tracking logic — with the bugs (default build) or with the fixes
 * (-DALL_FIXES).
 *
 * Build & run (from the formal/ directory):
 *     ./tests/run_tests.sh              # builds & runs BOTH unfixed and fixed
 *
 * or by hand, from formal/:
 *     CORE=$(find harnesses -name '*.c' ! -name '*_main.c' ! -name '*_bmc.c')
 *     cc            tests/tests.c $CORE -o /tmp/t_nofix && /tmp/t_nofix
 *     cc -DALL_FIXES tests/tests.c $CORE -o /tmp/t_fix   && /tmp/t_fix
 *
 * You can also enable a SINGLE fix instead of all of them, e.g.
 *     cc -DFIX_APPLY_MASK_CONSIST tests/tests.c $CORE ...
 * (the fix macros are listed in common/fixes.h).
 *
 * ADD YOUR OWN CASES: write a test_*() function following test_marat()
 * below and call it from main(). The helpers — mk_alu(), set_reg(),
 * run(), print_reg(), expect() — are all you need. Nothing here depends
 * on Frama-C; it is a plain C program.
 */
#include <stdio.h>
#include <inttypes.h>
#include "../harnesses/eval_alu/eval_alu.h"

/* ---- helpers -------------------------------------------------------- */

/*
 * Build one ALU instruction.
 *   cls = BPF_ALU (32-bit op) or EBPF_ALU64 (64-bit op)
 *   op  = BPF_ADD, BPF_SUB, BPF_AND, ... EBPF_MOV, BPF_NEG, ...
 *   src = BPF_K (operand is the immediate) or BPF_X (operand is src_reg)
 */
static struct ebpf_insn
mk_alu(uint8_t cls, uint8_t op, uint8_t src, uint8_t dst_reg,
       uint8_t src_reg, int32_t imm)
{
	struct ebpf_insn ins;
	ins.code = cls | op | src;
	ins.dst_reg = dst_reg;
	ins.src_reg = src_reg;
	ins.off = 0;
	ins.imm = imm;
	return ins;
}

/* Pin a register's tracked description directly. */
static void
set_reg(struct bpf_reg_val *r, uint64_t mask,
	int64_t smin, int64_t smax, uint64_t umin, uint64_t umax)
{
	r->v.type = RTE_BPF_ARG_RAW;        /* a defined scalar */
	r->v.size = sizeof(uint64_t);
	r->v.buf_size = 0;
	r->mask = mask;
	r->s.min = smin;
	r->s.max = smax;
	r->u.min = umin;
	r->u.max = umax;
}

/* A fresh evaluation state with every register a defined scalar 0. */
static void
init_state(struct bpf_eval_state *st)
{
	for (int i = 0; i < EBPF_REG_NUM; i++)
		set_reg(&st->rv[i], _64_BIT_MASK, 0, 0, 0, 0);
}

static void
print_reg(const char *label, const struct bpf_reg_val *r)
{
	printf("    %-11s mask = 0x%016" PRIx64 "\n", label, r->mask);
	printf("    %-11s s = [%20" PRId64 ", %20" PRId64 "]\n",
	       "", r->s.min, r->s.max);
	printf("    %-11s u = [%20" PRIu64 ", %20" PRIu64 "]\n",
	       "", r->u.min, r->u.max);
}

/* Run one instruction on register `dst` of the state; print the verdict. */
static const char *
run(struct bpf_verifier *bvf, const struct ebpf_insn *ins)
{
	const char *err = eval_alu(bvf, ins);
	printf("    eval_alu -> %s\n", err ? err : "NULL (instruction accepted)");
	return err;
}

/* Compare a register against an expected description; report match. */
static int
expect(const struct bpf_reg_val *got, uint64_t mask,
       int64_t smin, int64_t smax, uint64_t umin, uint64_t umax)
{
	int ok = got->mask == mask &&
		 got->s.min == smin && got->s.max == smax &&
		 got->u.min == umin && got->u.max == umax;
	printf("    expected     mask = 0x%016" PRIx64 "\n", mask);
	printf("    %-11s s = [%20" PRId64 ", %20" PRId64 "]\n", "", smin, smax);
	printf("    %-11s u = [%20" PRIu64 ", %20" PRIu64 "]\n", "", umin, umax);
	printf("    ==> %s\n", ok ? "MATCHES expectation"
				    : "DIFFERS from expectation");
	return ok;
}

/* ---- test cases ----------------------------------------------------- */

/*
 * Marat's example. Start with a 64-bit register known to hold -2 or -1.
 * Do a 32-bit `ADD 0` (hardware keeps the low 32 bits and zero-extends),
 * then a 64-bit `ADD 1`. The question is whether the tracked ranges stay
 * faithful across the 32->64 width change — i.e. whether the signed range
 * is correctly re-read at the new mask instead of desyncing.
 */
static void
test_marat(void)
{
	struct bpf_eval_state st;
	struct bpf_verifier bvf = { .evst = &st };
	struct bpf_reg_val *r = &st.rv[0];
	struct ebpf_insn ins;

	puts("======================================================================");
	puts("Marat's example: 64-bit [-2,-1]  --ALU32 ADD 0-->  --ALU64 ADD 1-->");
	puts("======================================================================");

	init_state(&st);

	/* Start: a 64-bit register known to be -2 or -1. */
	set_reg(r, _64_BIT_MASK, -2, -1, (uint64_t)-2, (uint64_t)-1);
	puts("\n  [start] 64-bit register, value is -2 or -1:");
	print_reg("start", r);

	/* Instruction 1: BPF_ALU | BPF_ADD | BPF_K, imm = 0  (32-bit add of 0). */
	puts("\n  [ins1] ALU32  ADD  K  #0   (32-bit: keep low 32 bits, zero-extend)");
	ins = mk_alu(BPF_ALU, BPF_ADD, BPF_K, 0, 0, 0);
	run(&bvf, &ins);
	print_reg("result", r);
	puts("  Marat's expectation after ins1:");
	expect(r, _32_BIT_MASK, -2, -1,
	       (uint64_t)UINT32_MAX - 1, (uint64_t)UINT32_MAX);

	/* Instruction 2: BPF_ALU64 | BPF_ADD | BPF_K, imm = 1  (64-bit add of 1). */
	puts("\n  [ins2] ALU64  ADD  K  #1   (64-bit: full width)");
	ins = mk_alu(EBPF_ALU64, BPF_ADD, BPF_K, 0, 0, 1);
	run(&bvf, &ins);
	print_reg("result", r);
	puts("  Marat's expectation after ins2:");
	expect(r, _64_BIT_MASK,
	       (int64_t)UINT32_MAX, (int64_t)UINT32_MAX + 1,
	       (uint64_t)UINT32_MAX, (uint64_t)UINT32_MAX + 1);

	puts("");
}

/*
 * Probe: does a 32-bit self-xor leave the register's mask field at the
 * op width (U32), or does the zeroing set it to U64? This decides whether
 * "mask == op width" is a maintained invariant or too strong.
 */
static void
test_selfxor_mask(void)
{
	struct bpf_eval_state st;
	struct bpf_verifier bvf = { .evst = &st };
	struct bpf_reg_val *r = &st.rv[0];
	struct ebpf_insn ins;

	puts("======================================================================");
	puts("Probe: 32-bit self-xor (ALU32 XOR X, dst=src=r0) — what is r0.mask?");
	puts("======================================================================");

	init_state(&st);
	set_reg(r, _64_BIT_MASK, -5, 7, 0, (uint64_t)-1);   /* any defined reg */

	ins = mk_alu(BPF_ALU, BPF_XOR, BPF_X, 0, 0, 0);
	run(&bvf, &ins);
	print_reg("result", r);
	printf("    op width (alu_msk) = 0x%016" PRIx64 "\n", (uint64_t)_32_BIT_MASK);
	printf("    ==> mask %s op width\n",
	       r->mask == _32_BIT_MASK ? "EQUALS" : "DIFFERS from");
	puts("");
}

/* ---- entry point ---------------------------------------------------- */

int main(void)
{
#ifdef ALL_FIXES
	puts("### build: WITH ALL FIXES  (-DALL_FIXES) ###\n");
#else
	puts("### build: NO FIXES  (faithful upstream semantics) ###\n");
#endif

	test_marat();
	test_selfxor_mask();

	/* Add your own test_*() calls here. */

	return 0;
}
