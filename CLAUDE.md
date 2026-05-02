# Fiat Cryptography


## Custom notes, agent workflows, and organization

There are special markdown files in this dir, each with distinct roles.

CLAUDE.md:
high level project info, the goal of the project, codebase organization, all time-independent and ideally fully trustworthy. Only update when we make a big change, significant refactor, etc. ask before updating this.

NOTES.md:
Random discoveries and patterns that we've discovered, explanations of issues, more detailed info that might be relevant in the future but won't be relevant for every task.
DONT put random task-specific planning stuff in NOTES. this is for generally true facts and patterns, not planning. 

NOTES.md should only be scraped when we are stuck or need some detailed info, in which case a grep might turn something up. Add to NOTES.md whenever we expend lots of effort to discover something specific that might be relevant later.


## Safe vs developing code

Most of the codebase was written before me and is trustworthy but also confusing. There is a lot of complex code to do simple things, so always check the README for anything high-level before going into code.
I am working on adding vectorized instructions to the system. Most of this happens in 

src/Assembly/Syntax.v
src/Assembly/Symbolic.v
src/Assembly/WithBedrock/Semantics.v
src/Assembly/WithBedrock/SymbolicProofs.v (mainly one large proof at the end)

src/SIMDBatch.v is a new developmental file to batch IR programs.

If you ever need examples of how to do something, the best choice is mirroring an analogous solution in the existing code for scalar instructions. Never trust the existing vector implementations, otherwise we are copying our own code that might already be misleading.


## Commands

### Building

make -j 9 [file].vo 
to build a specific file using 9/10 cores of my laptop.
you can compile files directly with rocq, but usually make is better.

### Equivalence checker and synthesis CLI

**Preferred: use the test runner.** All equivalence check tests are registered in `test-asm/test-manifest.tsv` and run via `./test-asm/run-tests.sh`. Use this instead of invoking the CLI directly whenever the test you want is in the manifest:
```
./test-asm/run-tests.sh              # run all tests
./test-asm/run-tests.sh -v           # verbose (show checker output on failure)
./test-asm/run-tests.sh -c batch     # filter by category
./test-asm/run-tests.sh -n avx-xmm-add  # run a single test by name
```
Every test in the manifest is run and reported as PASS, FAIL, or SKIP.

**Direct CLI invocation** — only needed for one-off checks not in the manifest, synthesis, or debugging. The CLI binaries live in `src/ExtractionOCaml/`. Build with:
```
make -j9 src/ExtractionOCaml/unsaturated_solinas
```

Basic synthesis (no equivalence checking). Use exactly the parameters from `fiat-c/src/curve25519_64.c` line 1:
```
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier 25519 64 '(auto)' '2^255 - 19' add -o output.c
```
This generates C code for the `add` operation on curve25519 with 64-bit limbs. Note: `25519` not `curve25519`, and `(auto)` for limb count. Using `curve25519` causes a stack overflow.

Equivalence checking adds `--hints-file` to compare assembly against the synthesized PHOAS expression:
```
src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier 25519 64 '(auto)' '2^255 - 19' add \
  --hints-file path/to/assembly.asm \
  -o /dev/null --output-asm /dev/null
```
If the check passes, it exits cleanly. If it fails, you get an error like `Unable_to_unify` or `Symbolic_execution_failed`.

The output will often be huge and include tons of detailed info. You usually only need the end of it, something like the last 40 lines. Remember this when using the equivalence checker!

**Assembly file format** (Intel syntax, not AT&T):
```asm
SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	mov rax, [rsi]
	add rax, [rdx]
	mov [rdi], rax
	ret
```
- Must have `SECTION .text`, `GLOBAL label`, `label:`, and `ret`
- The label name must match the function name the checker generates (e.g. `fiat_25519_add` for curve25519 add). By default prefix/suffix matching is allowed; `--asm-label-exact-match` forces exact.
- Memory operands use brackets: `[rsi + 16]`, `[rax + 8*rcx]`
- Hex constants: `0x10` (not bare decimal for offsets, though decimal works for immediates)

**Useful flags** (found in `src/CLI.v`):
- `--hints-file FILE`: assembly to check (can pass multiple)
- `--asm-stack-size N`: stack size in bytes (auto-inferred if omitted)
- `--asm-reg r1,r2,...`: calling convention registers (default: System V AMD64 = rdi,rsi,rdx,rcx,r8,r9)
- `--no-error-on-unused-asm-functions`: don't fail if .asm has extra labels
- `--debug-asm-symex-first`: run assembly symex before PHOAS symex (useful for debugging parse/symex errors in isolation)

**How it works internally** (relevant files for debugging):
1. `src/Assembly/Parse.v` — `parse_Lines` turns the .asm text into a `Lines` AST
2. `src/Assembly/Equivalence.v` — `check_equivalence` (around line 1476) is the core: it runs `symex_PHOAS` on the spec and `symex_asm_func` on the parsed assembly, then compares the resulting DAGs
3. The PHOAS expression comes from the synthesis pipeline (BoundsPipeline), not from C — the C output is just stringification of the same PHOAS

**Existing test examples** are in `Makefile.test-amd64-files.mk` and `fiat-amd64/` — those are scalar programs that have been verified against known-good assembly. Good reference for invocation patterns.

**How this was figured out**: grepping for `--hints-file` in CLI.v, reading Equivalence.v's `check_equivalence` section, and tracing the Makefile test targets in `Makefile.test-amd64-files.mk`.



## Doing proofs, compiling, checking errors

If a proof is not compiling, stop after the first failed fix attempt and explain the problem to me. Do not try multiple approaches or workarounds. Warnings are usually fine.
When checking errors after compiling a recent edit, you usually need a fair amount of context, e.g. grep -60

If you are adding any kind of Gallina/rocq code, always compile to see if it typechecks. if there is something that you expected to work that doesnt, either fix it or ask for help.




## Other background info


SYNTHESIS PATH (what fiat-crypto does internally):
  ═══════════════════════════════════════════════════

    Mathematical Spec (Coq)          e.g., addmod in Arithmetic/ModOps.v
             │
             │ reification (Derive)
             ▼
    PHOAS Expression                 e.g., reified_add_gen in
  UnsaturatedSolinasReificationCache.v
             │
             │ Pipeline.BoundsPipeline (optimization, partial eval, bounds)
             ▼
    Optimized PHOAS Expression       still API.Expr type
             │
             │ Stringification
             ▼
    C code                           e.g., fiat_25519_add in field_add.c


  EQUIVALENCE CHECKING PATH (when --hints-file is passed):
  ════════════════════════════════════════════════════════

    Optimized PHOAS Expr              External Assembly (--hints-file)
             │                                   │
             │ symex_PHOAS                       │ parse + symex_asm
             ▼                                   ▼
          DAG (IR)  ◄─────── compare ───────►  DAG (IR)
             │                                   │
             └───────────── equal? ──────────────┘
                              │
                        if yes: output verified assembly
                        if no:  error


SIMD batched programs
  ════════════════════════════════════════════════════════

Eventual goal:
PHOAS is transformed into a batched program which runs the same operations on multiple inputs
should emulate an ISPC-compiled AVX program like:

```
// Batched field addition for curve25519
// This is a direct, trivial translation of fiat_25519_add
// Each SIMD lane computes one independent field addition

export void batched_field_add(
    uniform uint64 out1[],    // out1[count * 5] - output field elements
    uniform uint64 arg1[],    // arg1[count * 5] - first input
    uniform uint64 arg2[],    // arg2[count * 5] - second input
    uniform int count
) {
    foreach (i = 0 ... count) {
        // Literally the same as fiat_25519_add, just indexed by i
        uint64 x1 = arg1[i * 5 + 0] + arg2[i * 5 + 0];
        uint64 x2 = arg1[i * 5 + 1] + arg2[i * 5 + 1];
        uint64 x3 = arg1[i * 5 + 2] + arg2[i * 5 + 2];
        uint64 x4 = arg1[i * 5 + 3] + arg2[i * 5 + 3];
        uint64 x5 = arg1[i * 5 + 4] + arg2[i * 5 + 4];
        out1[i * 5 + 0] = x1;
        out1[i * 5 + 1] = x2;
        out1[i * 5 + 2] = x3;
        out1[i * 5 + 3] = x4;
        out1[i * 5 + 4] = x5;
    }
}
```
