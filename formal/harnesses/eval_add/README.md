From `formal/` run
```
frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_add \
	-wp-prop=-usound,-ssound \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 120 \
	-wp-fct eval_add \
	-wp-prop=usound,ssound \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c
```
for the original (not fixed) code, or run
```
frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_add \
	-wp-prop=-usound,-ssound \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 120 \
	-wp-fct eval_add \
	-wp-prop=usound \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c

frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 120 \
	-wp-fct eval_add \
	-wp-prop=ssound \
	harnesses/eval_add/eval_add.c \
	harnesses/eval_fill_max_bound/eval_fill_max_bound.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c \
	harnesses/eval_umax_bound/eval_umax_bound.c
```
for the fixed code.
