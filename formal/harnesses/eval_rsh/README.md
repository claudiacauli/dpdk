From `formal/` run
```
frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_rsh \
	-wp-prop=-usound,-ssound \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c

frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_rsh \
	-wp-prop=usound,ssound \
	harnesses/eval_rsh/eval_rsh.c \
	harnesses/eval_max_bound/eval_max_bound.c \
	harnesses/eval_smax_bound/eval_smax_bound.c
```
