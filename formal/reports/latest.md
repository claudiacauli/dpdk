# Verification results

Cell order: **CBMC · ESBMC · WP**. Glyphs: Y proved, X violated (counterexample), T timeout/unknown, ! fails by design (intentional wraparound), - not applicable.

## Contract properties

| method | sfull32 | sfull64 | unchanged_u | unchanged_mask | unchanged_v | sord | swidth | ufull | umax_ok | unchanged_s | uord | uwidth | valid | consist_min | consist_max | mask_set | mask_ok | type_raw | unchanged_size | unchanged_buf | type_ok | umin64 | umax64 | uwiden32 | ukeep32 | smin32 | smax32 | smin64 | smax64 | usound | ssound |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| eval_smax_bound | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- |
| eval_umax_bound | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- |
| eval_max_bound | Y·Y·Y | Y·Y·Y | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·Y | -·-·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- |
| eval_fill_max_bound | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·Y | -·-·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- |
| eval_apply_mask | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y |
| eval_sub | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y |
| eval_add | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | -·-·- | Y·Y·Y | Y·Y·T |

## Memory safety / UB checks

| method | bounds | pointer | division | signed-overflow | unsigned-overflow | shift | memory-leak | nan | struct-fields | data-races | deadlock | lock-order | atomicity |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| eval_smax_bound | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_umax_bound | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_max_bound | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_fill_max_bound | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_apply_mask | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | !·!·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_sub | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | !·!·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |
| eval_add | Y·Y·Y | Y·Y·Y | Y·Y·- | Y·Y·- | !·!·- | Y·Y·- | Y·Y·- | Y·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- | -·Y·- |

## Environment

- frama-c: 32.0 (Germanium)
- cbmc: 6.9.0 (cbmc-6.9.0)
- esbmc: ESBMC version 8.4.0 64-bit aarch64 macos
- z3: Z3 version 4.15.4 - 64 bit
- alt-ergo: v2.6.2
- host: Darwin arm64
