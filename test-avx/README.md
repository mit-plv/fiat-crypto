# test-avx/

Test bench for the AVX equivalence checker. Each `.asm` file implements a curve25519 field operation using either scalar, XMM, or YMM instructions, and is verified against the corresponding PHOAS spec via the synthesis CLI.

## Running tests

All tests are registered in `test-manifest.tsv` and run by `run-tests.sh` from the repo root:

```sh
./test-avx/run-tests.sh              # run all
./test-avx/run-tests.sh -v           # verbose (show checker output on failure)
./test-avx/run-tests.sh -c batch     # filter by category
./test-avx/run-tests.sh -n avx-xmm-add  # single test by name
```

Requires the CLI binary to be built first: `make -j9 src/ExtractionOCaml/unsaturated_solinas`

## Benchmarks

### Equivalence checking time

```sh
./test-avx/bench-equiv-check.sh [RUNS]   # default: 3 runs per test
```

Outputs a TSV with name, category, instruction count, average checking time, and result for each test in the manifest.

### Native AVX2 runtime performance (requires x86-64 Linux with AVX2)

```sh
# Generate the C source files first:
./test-avx/bench_avx_native.sh

# Or use the full benchmark (after copying files to an x86-64 machine):
# 1. Assemble: nasm -f elf64 -o batch_avx_add.o batch_avx_add.asm (etc.)
# 2. Compile: gcc -O2 -o bench_all bench_all.c *.o
# 3. Run: taskset -c 0 ./bench_all
```

See `RESULTS.md` for full results on AMD EPYC 7502P.

### C-level baseline (any platform)

```sh
# Generate C source (from repo root):
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' add -o test-avx/gen_scalar_add.c
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' carry --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 -o test-avx/gen_scalar_carry.c
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' carry_mul --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 -o test-avx/gen_scalar_carry_mul.c
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' batch_add -o test-avx/gen_batch_add.c
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' batch_carry --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 -o test-avx/gen_batch_carry.c
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' batch_carry_mul --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 -o test-avx/gen_batch_carry_mul.c

# Compile and run:
cc -O2 -o test-avx/bench_runtime test-avx/bench_runtime.c
./test-avx/bench_runtime
```

## run-tests.sh

Reads `test-manifest.tsv` line by line. Each row specifies a test name, category, the CLI binary, curve parameters, operation name, assembly file, and optional extra flags. The script invokes the equivalence checker with `--hints-file` and reports:

- **PASS** -- equivalence check succeeded
- **FAIL** -- equivalence check failed
- **SKIP** -- binary not built or asm file missing

Verbose mode (`-v`) dumps the last 80 lines of checker output on failure and saves full output to `/tmp/test_output_<name>.txt`.

## test-manifest.tsv

TSV with columns: `name`, `category`, `binary`, `curve_name`, `bitwidth`, `limbs`, `prime`, `operation`, `asm_file`, `extra_flags`. The `operation` field (e.g. `add`, `batch_add`, `carry_mul`) selects which PHOAS spec the checker synthesizes and compares against.

## Assembly files

### Limb-parallel (single field element, SIMD across limb pairs)

| File | Width | Operation | Description |
|------|-------|-----------|-------------|
| `simple_avx_add.asm` | XMM | `add` | `vpaddq` on pairs of limbs, `vmovq` for the 5th |
| `simple_avx_add_ymm.asm` | YMM | `add` | `vpaddq ymm` for limbs 0-3, scalar for limb 4 |
| `simple_avx_sub.asm` | XMM | `sub` | XMM sub with balance constants |
| `simple_avx_sub_ymm.asm` | YMM | `sub` | YMM sub with `vpbroadcastq` + `vpblendd` for balance |

### Batched (4 independent field elements in parallel)

| File | Layout | Operation | Description |
|------|--------|-----------|-------------|
| `batch_avx_add.asm` | SoA | `batch_add` | 5 × YMM load/add/store, contiguous |
| `batch_avx_sub.asm` | AoS (contiguous) | `batch_sub` | 5 × YMM sub with rotating balance vector |
| `batch_avx_opp.asm` | AoS (contiguous) | `batch_opp` | 5 × YMM sub from balance constants |
| `batch_avx_carry.asm` | AoS (gather/scatter) | `batch_carry` | Gather → SIMD carry chain → scatter |
| `batch_avx_carry_add.asm` | AoS (gather/scatter) | `batch_carry_add` | Fused add + carry, gather/scatter |
| `batch_avx_carry_sub.asm` | AoS (gather/scatter) | `batch_carry_sub` | Fused sub + carry, gather/scatter |
| `batch_avx_carry_opp.asm` | AoS (gather/scatter) | `batch_carry_opp` | Fused opp + carry, gather/scatter |
| `batch_scalar_carry.asm` | AoS | `batch_carry` | 4x scalar carry (no SIMD) |
| `batch_scalar_carry_mul.asm` | AoS | `batch_carry_mul` | 4x scalar carry_mul (no SIMD) |

### Other

| File | Description |
|------|-------------|
| `synthesized_avx_add.asm` | Machine-generated AVX add (experimental, not in manifest) |
| `carry_mul_32.c` | Reference 32-bit carry_mul C code |

## Memory layouts

- **SoA (Structure of Arrays):** All limb_i values across elements are contiguous. `batch_avx_add` uses this: `[e0_l0, e1_l0, e2_l0, e3_l0, e0_l1, ...]`. Each YMM load gets the same limb from all 4 elements.

- **AoS (Array of Structures):** Elements are contiguous: `[e0_l0, e0_l1, ..., e0_l4, e1_l0, ...]`. Two sub-cases:
  - **Contiguous:** Operations that process 4 consecutive uint64s per YMM without caring which limb they are (add/sub/opp). Each YMM spans parts of adjacent elements.
  - **Gather/scatter:** Operations that need all 5 limbs of each element in the same SIMD lane (carry). Requires transposing the data into YMM registers at function entry and back at exit.

## Performance summary

On AMD EPYC 7502P (AVX2, no AVX-512), comparing hand-written AVX2 assembly to 4x noinline scalar C:

| Category | Speedup | Reason |
|----------|---------|--------|
| add/sub/opp (contiguous loads) | **3–7x** | Direct YMM load/op/store, no transpose |
| limb-parallel XMM | **1.1–1.5x** | 2 limbs per instruction, 5th limb scalar |
| carry (gather/scatter) | **0.7–1.0x** | Transpose cost exceeds SIMD savings |
| carry_opp (gather/scatter) | **1.4–2.1x** | Opp is cheap enough to offset transpose |

See `RESULTS.md` for detailed numbers and analysis.

## Where the batched PHOAS specs live

The batched operations (`batch_add`, `batch_sub`, `batch_carry`, `batch_carry_mul`, etc.) are defined in:

1. **`src/PushButtonSynthesis/SIMDUnsaturatedSolinas.v`** -- mathematical specs (`batched_addmod`, `batched_submod`, `batched_carrymod`, `batched_carry_mulmod`) and reified PHOAS forms. Each batched op applies the scalar operation independently to 4 slices of a flat `4*n`-element input list.

2. **`src/PushButtonSynthesis/UnsaturatedSolinas.v`** -- wires reified specs into `BoundsPipeline` (the definitions `batch_add`, `batch_sub`, `batch_carry`, `batch_carry_mul` around lines 362-424) and registers them as CLI operations in the `known_functions` dispatch table (around line 1024).

The scalar specs they build on (`addmod`, `carry_mulmod`, etc.) come from `src/Arithmetic/ModOps.v`.

## Encoding note

`vpandq`/`vpxorq` in the carry-variant `.asm` files use AVX-512 VL encoding (EVEX prefix). On AVX2-only hardware, substitute `vpand`/`vpxor` (VEX prefix) — semantically identical for 128/256-bit operands. The equivalence checker handles both; runtime benchmarks use the VEX versions.
