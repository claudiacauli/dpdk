From `formal/` run
```
frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_arsh \
	-wp-prop=-usound,-ssound \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c

frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_arsh \
	-wp-prop=usound,ssound \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c
```
for the original (not fixed) code, or run
```
frama-c -cpp-extra-args=-DALL_FIXES -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
	-wp-fct eval_arsh \
	-wp-prop=-usound,-ssound \
	harnesses/eval_arsh/eval_arsh.c \
	harnesses/eval_max_bound/eval_max_bound.c
```
