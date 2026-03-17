# Fiat Cryptography


## Custom notes, agent workflows, and organization

There are 3 special markdown files in this dir, each with distinct roles.

CLAUDE.md:
high level project info, the goal of the project, codebase organization, all time-independent and ideally fully trustworthy. Only update when we make a big change, significant refactor, etc. ask before updating this.

ACTIVE_CONTEXT.md:
Working ideas, todos, the state of the project and what to do next. Updated after every task or when we change our plan in any way.
Do not change the format of this file. This file should be continuously updated but stay relatively concise and readable. Old issues and completed items should be completely removed. 
This file is for both me an agents, so clarify who should be working on something if its ambiguous. E.g. proofs are always for me unless otherwise stated.
DO NOT put random facts, insights, etc in here. those should go in NOTES, and ony if they will be relevant in the future.

NOTES.md:
Random discoveries and patterns that we've discovered, explanations of issues, more detailed info that might be relevant in the future but won't be relevant for every task.
DONT put random task-specific planning stuff in NOTES. this is for generally true facts and patterns, not planning. 

Every high-level agent should read CLAUDE.md and ACTIVE_CONTEXT.md. Subagents which do specific tasks might not need these.
NOTES.md should only be scraped when we are stuck or need some detailed info, in which case a grep might turn something up. Add to NOTES.md whenever we expend lots of effort to discover something specific that might be relevant later.


## Safe vs developing code

Most of the codebase was written before me and is trustworthy but also confusing. There is a lot of complex code to do simple things, so always check the README for anything high-level before going into code.
I am working on adding vectorized instructions to the system. Most of this happens in 

src/Assembly/Syntax.v
src/Assembly/Symbolic.v
src/Assembly/WithBedrock/Semantics.v
src/Assembly/WithBedrock/SymbolicProofs.v (mainly one large proof at the end)

src/SIMDBatch.v is a new developmental file to batch IR programs.
test-asm/ contains developmental test assembly files:
  - simple_scalar_add.asm — baseline scalar add, works with existing checker
  - simple_avx_add.asm — XMM vectorized add using lanes 0+1, PASSES equivalence check
  - simple_avx_add_lane1.asm — XMM lane 1 variant (vpunpcklqdq + vpextrq), needs symex for those instrs
  - simple_avx_add_lane2.asm — YMM lane 2 variant (vperm2i128 + vextracti128), needs symex for those instrs
  - simple_avx_add_lane3.asm — YMM lane 3 variant (all of the above combined), needs symex for those instrs
  - wrapped_avx_add.asm — full batched AVX2 add with gather/scatter, future goal
  - check-simple-add.sh — runs equivalence check on simple_avx_add.asm, prints PASS/FAIL
  - test_add.c / test_add.sh — C test harness, runs on remote (ARM Mac can't run x86 asm)

I don't fully understand the high-level structure, but so far I've added some instructions, helper functions to modularize vectorized instructions, proof of correctness for these, and reworked the register system slightly to include AVX registers. There was no vectorized instruction code before me, so all of that is potentially wrong (not buggy, but perhaps misled- it can be refactored). All other code is old and probably correct, so if we consider changing it, we need a very good reason. 

If you ever need examples of how to do something, the best choice is mirroring an analogous solution in the existing code for scalar instructions. Never trust the existing vector implementations, otherwise we are copying our own code that might already be misleading.


## Commands

### Building

make -j 9 [file].vo 
to build a specific file using 9/10 cores of my laptop.

make clean 
make -j 9
to reset if things get really messed up - dont do this, ask me to do it for you
you can compile files directly with rocq, but usually make is better. Im not experienced enough to know why or when.

I have a remote server that runs linux and can do some faster computation, but with really bad latency. not that useful, but if you have a really specific use case where you think this will be good, let me know. NEVER use this for super basic things that you could do locally.

### Equivalence checker and synthesis CLI

**Preferred: use the test runner.** All equivalence check tests are registered in `test-asm/test-manifest.tsv` and run via `./test-asm/run-tests.sh`. Use this instead of invoking the CLI directly whenever the test you want is in the manifest:
```
./test-asm/run-tests.sh              # run all tests
./test-asm/run-tests.sh -v           # verbose (show checker output on failure)
./test-asm/run-tests.sh -c batch     # filter by category
./test-asm/run-tests.sh -n avx-xmm-add  # run a single test by name
```
The manifest tracks expected status (`pass`/`fail`/`skip`). When a previously-failing test starts passing, the runner reports `XPASS` — update the manifest to `pass`.

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




## Adding a new instruction (three-file pattern)

1. `src/Assembly/Syntax.v` — add OpCode constructor + `accesssize_of_declaration` case (return `None`)
2. `src/Assembly/WithBedrock/Semantics.v` — add concrete semantics to `DenoteNormalInstruction`
3. `src/Assembly/Symbolic.v` — add symbolic semantics to `SymexNormalInstruction`

Sometimes also `src/Assembly/Equality.v` if the MEM type changes (e.g. adding a new field).

OpCode constructors auto-register in the string parser via `Derive OpCode_Listable` — no extra parser work needed.


## DAG rewrite rules (Symbolic.v)

The equivalence checker compares two DAGs (one from PHOAS, one from assembly symex). Before comparison, each DAG node is simplified by rewrite rules in `Module Rewrite` in Symbolic.v.

**How they work:**
1. Each rule is a function `dag -> expr -> expr` that pattern-matches on an expression and returns a simplified version (or the original if no match).
2. Each rule needs: a `Definition`, a `description_of` instance, and a `Global Instance ... : Ok ...` proof (typically `t. f_equal. Z.bitblast. Qed.`).
3. Rules are registered in three places:
   - `Variant rewrite_pass` (around line 326) — add a constructor
   - `default_rewrite_pass_order` (around line 370) — add to the list (ORDER MATTERS)
   - `named_pass` (around line 3800) — add the dispatch case
4. Rules are applied in list order, each getting one pass over the expression. If rule A creates a pattern that rule B should match, A must come before B.

**Key rules for SIMD (added by us):**
- `slice_slice`: `slice lo1 s1 (slice lo2 s2 [e])` → `slice (lo2+lo1) s1 [e]` when `lo1+s1 <= s2`
- `slice_set_slice`: `slice lo1 s1 (set_slice lo2 s2 [_, val])` → `slice (lo1-lo2) s1 [val]` when slice range is within set_slice range
- `slice_set_slice_disjoint`: `slice lo1 s1 (set_slice lo2 s2 [base, _])` → `slice lo1 s1 [base]` when ranges don't overlap
- `set_slice_set_slice`: `set_slice lo s (set_slice lo s [x, _], y)` → `set_slice lo s [x, y]` when inner is overwritten
- `slice_tower` (fuel-recursive): normalizes `slice lo sz [inner]` through *arbitrary interleaved* nested slice/set_slice layers in one pass — peels nested slices (combining offsets), disjoint set_slices (descends to base), and containing set_slices (descends to val). Needed for gather towers (vmovq→vpunpcklqdq→vinserti128) where a single application of the individual rules above stops after peeling one layer, because subsequent passes don't see the newly exposed nested slice/set_slice underneath.

**Why these matter for SIMD:** XMM registers are modeled as `slice 0 128` of YMM (256-bit). Reading an XMM wraps in `slice 0 128`, writing wraps in `set_slice 0 128`. vpaddq on XMM produces results wrapped in set_slice layers. Without these rules, the DAG has chains like `slice 0 64 (slice 0 128 (set_slice 64 64 [...]))` that don't simplify to the underlying `add 64` operation, causing equivalence to fail.

**Note:** The PHOAS rewriter (`rewriter/` submodule) is unrelated — it optimizes PHOAS expressions during synthesis. The DAG rewrite rules here operate during equivalence checking.

**IMPORTANT limitation:** Rewrite rules can see into subexpressions (via reveal depth), but when a rewrite rule PRODUCES new nested `ExprApp` subexpressions, those subexpressions are merged into the DAG without being simplified. See the DAG/App/Merge section below for why.


## DAG, App, Merge, and simplification (LLM interpretation — verify before relying on this)

The DAG is a flat array of nodes. Each node is `(op, list idx)` where `idx` is an index into the array. Expressions (`expr`) are trees: either `ExprRef idx` (pointer into DAG) or `ExprApp (op, list expr)` (nested tree).

**`App (node) : M idx`** (Symbolic.v ~4161) is the main way instructions insert nodes into the DAG. It:
1. Calls `simplify dag node` which does `reveal_node_at_least` (expands DAG refs into a nested expr tree to depth `node_reveal_depth`, default 3) then applies `Rewrite.expr` (the chain of rewrite passes).
2. Calls `merge expr dag` to insert the result.

**`merge` (Symbolic.v ~2044)** is a recursive `Fixpoint` that walks an `expr` tree:
- `ExprRef i` → returns `i` (already in DAG)
- `ExprApp (op, args)` → recursively merges each arg (getting their idx), then calls `merge_node (op, idxs)` which does `reverse_lookup` to find an existing matching `(op, idxs)` node or inserts a new one.

**Key consequence:** `merge` does NOT call `simplify` on subexpressions — it inserts them as-is via `merge_node`. Only `App` calls `simplify`, and only on its top-level node. So if a rewrite rule produces nested `ExprApp` nodes (e.g., `add 64 [slice 0 64 [slice 0 128 [...]]]`), the inner nodes are merged without simplification. This means a `slice 0 64 (slice 0 128 [...])` subexpression won't get the `slice_slice` rewrite applied to it.

**Why building incrementally matters:** When each sub-operation is created via its own `App` call (like in `make_lane`), each one independently gets simplified. If instead a rewrite rule constructs the same structure as nested `ExprApp` nodes in a single step, the inner nodes bypass simplification.

**Equivalence comparison:** `check_equivalence` in Equivalence.v compares output idx lists from PHOAS and ASM symex using `N.eqb` — the indices must be literally the same number. This works because both sides share the same DAG, and `merge` deduplicates: if ASM builds a node structurally identical to an existing PHOAS node, `merge_node`'s `reverse_lookup` finds it and returns the same idx.


## SymbolicProofs.v status

`src/Assembly/WithBedrock/SymbolicProofs.v` contains the correctness proof for symbolic execution. The `GetOperand_R` lemma (around line 744) currently fails because `Load` was extended to support 128/256-bit memory access (decomposed into multiple 64-bit loads). The proof needs new cases for these wider loads. The rest of the file should be fine.


## Instructions needing symbolic semantics

These opcodes are in Syntax.v (parser recognizes them) but do NOT yet have symbolic execution in Symbolic.v: `vpxor`, `vpunpcklqdq`, `vpunpckhqdq`, `vpextrq`, `vextracti128`, `vperm2i128`, `vpinsrd`, `vpgatherdq`, `vmovd`, `vpcmpeqd`, `vzeroupper`.

Adding symex for these will unblock the lane-variant test files and eventually `wrapped_avx_add.asm`.


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
