# test-asm/

Test assembly files for the AVX equivalence checker. Each file implements curve25519 field addition or subtraction using AVX instructions (XMM or YMM).


## Test files

| File | Status | What it tests |
|------|--------|---------------|
| `simple_avx_add.asm` | PASSES | XMM add. `vpaddq` on pairs of limbs, `vmovq` for the 5th. |
| `simple_avx_add_ymm.asm` | PASSES | YMM add. `vpaddq ymm` for limbs 0-3, scalar for limb 4. |
| `simple_avx_sub.asm` | FAILS | XMM sub. Needs `sub_to_add_neg` rewrite rule (was removed). |
| `simple_avx_sub_ymm.asm` | FAILS | YMM sub. Needs symex for: `vpbroadcastq`, `vpblendd`. |


## Test suite

All tests are registered in `test-manifest.tsv` and run via `run-tests.sh` from the repo root.

```sh
./test-asm/run-tests.sh           # run all tests
./test-asm/run-tests.sh -v        # verbose (show output on any failure)
./test-asm/run-tests.sh -c ymm    # filter by category
./test-asm/run-tests.sh -n avx-xmm-add  # run single test
```

The manifest tracks expected status (`pass`/`fail`/`skip`). When a previously-failing test starts passing (e.g., after adding a new instruction), the runner reports `XPASS` — update the manifest to `pass`.


## Files

| File | Purpose |
|------|---------|
| `run-tests.sh` | Runs all equivalence check tests from the manifest, reports pass/fail summary. |
| `test-manifest.tsv` | Registry of all tests with parameters and expected status. |


## Running individual equivalence checks

```sh
# From repo root:
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
  25519 64 '(auto)' '2^255 - 19' add \
  --hints-file test-asm/simple_avx_add.asm -o /dev/null --output-asm /dev/null

# For sub:
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
  25519 64 '(auto)' '2^255 - 19' sub \
  --hints-file test-asm/simple_avx_sub.asm -o /dev/null --output-asm /dev/null
```
