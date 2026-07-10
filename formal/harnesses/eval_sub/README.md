From `formal/` run
```
frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_sub \
	-wp-prop=-usound,-ssound \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_sub \
	-wp-prop=usound,ssound \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c
```
for the original (not fixed) code, or run
```
frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_sub \
	-wp-prop=-usound,-ssound \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_sub \
	-wp-prop=usound \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_sub \
	-wp-prop=ssound \
	harnesses/eval_sub/eval_sub.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c
```
for the fixed code.
