Active Context for Fiat Crypto
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed.
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.


# Current Focus
The high level of what we are currently working on.

- Building out a test suite of AVX assembly programs to drive incremental instruction/rewrite rule support.
- **Next big test: batch_avx_carry_mul via the 9×29-bit reduced-radix approach** (see NOTES.md 2026-04-11 "Real AVX2 curve25519 implementations…"). This is how avxecc and curve25519-dalek-ng actually do it. Synthesize curve25519 with `9 --no-wide-int` to get a pure-uint64 scalar reference; write an SoA AVX2 assembly that mirrors it lane-wise using vpmuludq/vpaddq/vpsrlq/vpandq (all already have symex).
- De-prioritized: 5×51-bit AoS carry_mul with hybrid scalar multiply. Real implementations don't do this.


# Recent Updates
What we've thought about or accomplished recently, as far as it's relevant to moving forward. Mention specific files edited.

- **10/10 tests pass**: add/sub × xmm/ymm + batch_add + batch_sub + scalar_carry_mul + batch_carry_mul + batch_scalar_carry + batch_avx_carry.
- **batch_avx_carry fixed** by new `slice_tower` rewrite rule (Symbolic.v:2629). Fuel-recursive normalizer that collapses *arbitrarily interleaved* slice/set_slice towers in a single rule application. Registered in `rewrite_pass` variant, `default_rewrite_pass_order`, `named_pass`. Detail in NOTES.md (2026-04-11 section).
- **Added `batch_carry` operation to the synthesis pipeline** (SIMDUnsaturatedSolinas.v, UnsaturatedSolinas.v). `batched_carrymod` defined in SoA-independent AoS style. Registered in `known_functions`.
- **Scalar batch_carry passes**: `test-asm/batch_scalar_carry.asm` — 4 independent scalar carry chains. Requires `--shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001` flags.
- **GetReg/SetReg**: generalized master's hardcoded `sz == 64` to `sz == widest_reg_size_of r` for SIMD register support. The `App (slice 0 sz, [v])` wrapping in both functions must be kept.
- **Key insight on vectorized carry_mul**: vpmuludq does 32×32→64, but curve25519 uses 51-bit limbs. No AVX2 instruction does 64×64→128. Realistic: vectorize carry/accumulation with vpaddq/vpsrlq, keep multiplies scalar.
- **Key insight on AoS vs SoA for carry**: batch_add/sub work with AoS because addition is element-wise. Carry has inter-limb deps → vectorizing needs gather/scatter (load same limb across 4 elements). Needs vpunpcklqdq, vinserti128, vpextrq, vextracti128.
- **`tools/dagviz/` built** (2026-04-11) — personal Python debugging tool for DAG dumps: parser, structural alignment, Textual TUI with divergence-walk stepper and follow mode, shape hashing, rewrite-rule simulator (for the SIMD slice rules), graphviz export. Subcommands: `stats`, `diverge`, `trace`, `dot`, `tui`. Used to diagnose the slice_tower issue before the fix.
------------------------------------------------------


# Active Issues & Blockers
These are the bugs/specific issues that we need to resolve to move forward.

- **SymbolicProofs.v `GetOperand_R`**: Needs updating for 128/256-bit Load cases.

------------------------------------------------------


# Next Steps
What to do immediately, in order of priority.

- **First: verify scalar equivalence works with 9-limb synthesis.** Run the checker against a known-good scalar assembly generated for the 9-limb 29-bit representation. `./src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier --no-wide-int 25519 64 9 '2^255 - 19' carry_mul` synthesizes cleanly; we need to either generate a matching scalar .asm or check that an existing one still validates. If scalar 9-limb fails, nothing else is worth trying.
- **Then: write `test-asm/batch_avx_carry_mul.asm`** as a mechanical SoA translation of the 9-limb scalar carry_mul (≈260 statements), using vpmuludq for each scalar multiply and vpaddq/vpsrlq/vpandq for accumulation and carry propagation. Register file is tight (9 a-limbs + 9 b-limbs + 9 accumulators > 16 YMM regs), so some reloading from stack or memory is expected.
- **Alternative to investigate**: fetch gfparith.c from `hchengv/avxecc` directly and adapt its `mpi29_gfp_mul_avx2` — likely closer to production-quality asm than anything we write fresh.
- Consider ISPC as a tool for generating vectorized assembly to test against the checker (lower priority now that we have a direct template).

# Other ideas
'Batching' a single primitive on the assembly side requires writing assembly code by hand (or Claude). for some instrs this is easy:
add -> vpadd, whole program batches nicely
for others it is complicated:
mulZ = 64x64->128 bit multiply, no avx equivalent. need to pull out lanes into scalar registers, do 4 serial multiplies, put back into ymm regs to continue.
we could use ISPC for this, but it will run into similar issues and make code that might not pass the checker without many extra rewrite rules (maybe this means we need those rules to begin with?)
The goal of fiat cryptography is to take any optimized asm code (whether by hand or stochastic) and certify that it is correct, if it is indeed correct. This means that basically any optimization that actually works should be recognizable by the equivalent checker and our rewrite rules. Writing these assembly programs is just a way to see which rewrite rules we need to include. Maybe there's a more efficient, automated way to do this?


check online implementations of avx carry mul