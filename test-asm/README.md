# test-asm/

Test bench for the AVX equivalence checker. Each `.asm` file implements a curve25519 field operation (add, sub, carry, carry_mul) using either scalar, XMM, or YMM instructions, and is verified against the corresponding PHOAS spec via the synthesis CLI.

## Running tests

All tests are registered in `test-manifest.tsv` and run by `run-tests.sh` from the repo root:

```sh
./test-asm/run-tests.sh              # run all
./test-asm/run-tests.sh -v           # verbose (show checker output on failure)
./test-asm/run-tests.sh -c batch     # filter by category
./test-asm/run-tests.sh -n avx-xmm-add  # single test by name
```

Requires the CLI binary to be built first: `make -j9 src/ExtractionOCaml/unsaturated_solinas`

## run-tests.sh

Reads `test-manifest.tsv` line by line. Each row specifies a test name, category, expected result (`pass`/`fail`/`skip`), the CLI binary, curve parameters, operation name, assembly file, and optional extra flags. The script invokes the equivalence checker with `--hints-file` and compares the exit code against the expected status:

- **PASS** -- equivalence check succeeded
- **FAIL** -- equivalence check failed
- **SKIP** -- binary not built or asm file missing

Verbose mode (`-v`) dumps the last 80 lines of checker output on failure and saves the full output to `/tmp/test_output_<name>.txt`.

## test-manifest.tsv

TSV with columns: `name`, `category`, `binary`, `curve_name`, `bitwidth`, `limbs`, `prime`, `operation`, `asm_file`, `extra_flags`. The `operation` field (e.g. `add`, `batch_add`, `carry_mul`) selects which PHOAS spec the checker synthesizes and compares against.

## Assembly files

| File | Category | Operation | Description |
|------|----------|-----------|-------------|
| `simple_avx_add.asm` | xmm | `add` | XMM add: `vpaddq` on pairs, `vmovq` for the 5th limb |
| `simple_avx_add_ymm.asm` | ymm | `add` | YMM add: `vpaddq ymm` for limbs 0-3, scalar for limb 4 |
| `simple_avx_sub.asm` | xmm | `sub` | XMM sub |
| `simple_avx_sub_ymm.asm` | ymm | `sub` | YMM sub |
| `synthesized_avx_add.asm` | -- | `add` | Machine-generated AVX add (not in manifest) |
| `batch_avx_add.asm` | batch | `batch_add` | Batched AVX2 add (4 independent adds, SoA layout) |
| `batch_avx_sub.asm` | batch | `batch_sub` | Batched AVX2 sub |
| `batch_avx_carry.asm` | batch | `batch_carry` | Batched AVX2 carry reduction |
| `batch_scalar_carry.asm` | batch | `batch_carry` | Batched carry using scalar instructions |
| `batch_scalar_carry_mul.asm` | batch | `batch_carry_mul` | Batched carry-multiply using scalar instructions |

## Where the batched PHOAS specs live

The batched operations (`batch_add`, `batch_sub`, `batch_carry`, `batch_carry_mul`) are defined in two files:

1. **`src/PushButtonSynthesis/SIMDUnsaturatedSolinas.v`** -- defines the mathematical specs (`batched_addmod`, `batched_submod`, `batched_carrymod`, `batched_carry_mulmod`) and their reified PHOAS forms (`reified_batched_add_gen`, etc.). Each batched op applies the scalar operation independently to 4 slices of a flat `4*n`-element input list.

2. **`src/PushButtonSynthesis/UnsaturatedSolinas.v`** -- wires the reified specs into `BoundsPipeline` (the definitions `batch_add`, `batch_sub`, `batch_carry`, `batch_carry_mul` around lines 362-424) and registers them as CLI operations in the `known_functions` dispatch table (around line 1024).

The scalar specs they build on (`addmod`, `carry_mulmod`, etc.) come from `src/Arithmetic/ModOps.v`.
