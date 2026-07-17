# Verification results — fixed

Cell order: **CBMC · ESBMC · WP**. Glyphs: Y proved, X violated (counterexample), T timeout/unknown, ! fails by design (intentional wraparound), - not applicable.

## Contract properties

| method | err_def | err_dom | noerr | type_ok | uord | sord | uwidth | swidth |
|---|---|---|---|---|---|---|---|---|
| eval_alu | T·T·Y | T·T·Y | T·T·Y | T·T·Y | T·T·Y | T·T·Y | T·T·Y | T·T·Y |

## Memory safety / UB checks

| method | bounds | pointer | division | signed-overflow | unsigned-overflow | shift | memory-leak | nan | struct-fields | data-races | deadlock | lock-order | atomicity |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| eval_alu | T·T·Y | T·T·Y | T·T·- | T·T·- | T·!·- | T·T·Y | T·T·- | T·T·- | -·T·- | -·T·- | -·T·- | -·T·- | -·T·- |

## Environment

- frama-c: 32.0 (Germanium)
- cbmc: 6.9.0 (cbmc-6.9.0)
- esbmc: ESBMC version 8.4.0 64-bit aarch64 macos
- z3: Z3 version 4.15.4 - 64 bit
- alt-ergo: v2.6.2
- host: Darwin arm64
