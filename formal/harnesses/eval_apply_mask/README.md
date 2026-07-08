From `formal/` run
```
frama-c -rte -wp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 20 \
	harnesses/eval_apply_mask/eval_apply_mask_main.c \
	harnesses/eval_apply_mask/eval_apply_mask.c \
	harnesses/eval_smax_bound/eval_smax_bound.c
```
