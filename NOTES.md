# Notes

Majority written by Claude Code.
Technical discoveries, debugging notes, and patterns that took effort to figure out.
Try to keep this file to information that will be continually relevant, learned patterns about the codebase, etc. NOT just things that are true right now (like a the state of built binaries).


## Real AVX2 curve25519 implementations use 9×29-bit (or 10×25.5-bit) limbs, not 5×51 (2026-04-11)

**Critical discovery for the batch_avx_carry_mul effort.**

Existing hand-tuned AVX2 implementations of curve25519 (avxecc, curve25519-dalek-ng, Faz-Hernández/López) do **not** use 5×51-bit limbs. They use reduced-radix representations specifically to fit multiplies into `vpmuludq` (32×32 → 64):

- **avxecc** (hchengv/avxecc on github): **9 limbs of 29 bits** each, SoA layout (one `__m256i` per limb, four field elements interleaved across lanes). Two 30-bit values multiply to ≤60 bits, well within 64.
- **curve25519-dalek-ng**: **10 limbs in radix 25.5** (i.e. alternating 26-bit and 25-bit limbs), also SoA.
- Both use `VMAC` = `vpmuludq` + `vpaddq`, plus `vpsrlq`/`vpandq` for carry propagation. No scalar extraction needed.

**Fiat-crypto can synthesize this.** `unsaturated_solinas 25519 64 9 '2^255 - 19' carry_mul --no-wide-int` produces curve25519 carry_mul with 9-limb 29-bit rep using pure uint64 arithmetic (no uint128 intermediates). This is directly translatable to an AVX2 SoA implementation with the existing symex support (vpmuludq, vpaddq, vpsrlq, vpandq, vmovdqu all already implemented).

**The old plan (5×51-bit AoS + hybrid scalar multiply)** — pulling lanes out of YMM for scalar multiplies and putting them back — is what avxecc explicitly avoided. It's not how real implementations are structured. We should pivot batch_avx_carry_mul to mirror avxecc's 9×29-bit SoA structure.

**Implementation sketch for `test-asm/batch_avx_carry_mul.asm`**:
1. Use `--no-wide-int 25519 64 9 '2^255 - 19' carry_mul` as the synthesis target.
2. Memory layout: 36 uint64s per group = 9 limbs × 4 field elements, SoA (limb 0 of all 4 first, then limb 1, etc.). Each YMM register holds one limb from 4 elements.
3. `vmovdqu` loads one limb across 4 elements; `vpmuludq` does lane-parallel multiplication; `vpaddq` accumulates; `vpsrlq` + `vpandq` propagates carries.
4. Structurally matches the scalar 9-limb carry_mul output line-for-line, modulo `op op op → vpop op op op` rename.
5. Register allocation: ymm0..ymm8 for the 9 a-limbs, ymm9..ymm17 for the 9 b-limbs is possible if we use stack for accumulators, or reload from memory.

Estimated scale: ~260 scalar statements in the reference C output × 4-way batch = a mechanical translation of a large but manageable program. No new symex needed.

**Reference**: https://github.com/hchengv/avxecc/blob/main/src/gfparith.c — `mpi29_gfp_mul_avx2` is the direct template.


## Rewrite passes are strictly top-down-once — the slice_tower lesson (2026-04-11)

**General pattern this reveals — highly relevant for any future rewrite rule work.**

`Rewrite.expr` is `List.fold_left` over the pass list. Each pass is a function `dag -> expr -> expr` that is applied ONCE to the top of the expression. It does **not** recurse into subexpressions, and it does **not** get re-invoked when an earlier pass in the list produces a pattern that a later pass could have simplified further up the chain.

Concretely: if pass A transforms `f(g(h(x)))` into `f(h(x))` (stripping g), and pass B only fires on `f(h(x))` → `f(x)`, then as long as B comes **after** A in the pass list, B will fire. But if B fires first (on the original `f(g(h(x)))`, which it can't match), B is done. A then strips g. Now the only way to simplify `f(h(x))` is if B runs *again later*. Multiple copies of B in the pass list is one workaround. But if the structure is deeply interleaved — e.g. f(g(f(g(h(x))))) — you need A/B/A/B alternation, and the number of alternations is unbounded.

For the SIMD gather pattern (vmovq → vpunpcklqdq → vinserti128), a lane extraction `slice 0 64 [ymm_state]` has to peel through interleaved `slice 0 256` and `set_slice` layers. Each of the three existing rules (`slice_slice`, `slice_set_slice`, `slice_set_slice_disjoint`) only handles one of the three layer kinds, so you need the alternation.

**The fix pattern: fuel-recursive normalizers inside one rule.** Instead of relying on pass-level iteration, write a `Fixpoint` helper that recurses on the tree internally, handling all the layer kinds in a single rule invocation. `peel_disjoint_set_slices` already used this pattern for disjoint set_slice peeling. `slice_tower_normalize` (Symbolic.v:2629) generalizes it to handle:
- nested `slice lo2 s2 [e']` → recurse with offset `lo2 + lo`
- disjoint `set_slice lo2 s2 [base; _]` → recurse on base
- containing `set_slice lo2 s2 [_; val]` → recurse on val with offset `lo - lo2`

All three in one pass, fuel=16. This is the "right" fix: any interleaving of the three layer kinds is collapsed in a single rule application, and there's no dependence on pass ordering.

**Proof structure for this pattern**: the helper lemma `slice_tower_normalize_eval` induction is on fuel, not on the expression. For each layer kind, destructure the args list carefully (`destruct args as [|x [|y [|z ?]]]`), test the boolean condition, and apply IH after establishing the Z-level equivalence via `t. f_equal. Z.bitblast.`. The Ok wrapper does NOT use `t` on the outer shell — `t` over-destructures a fuel-recursive call and generates "No such goal"; instead manually destructure the top-level match (`destruct e`, `destruct n as [op args]`, `destruct op`, destructure args list) and then call the helper lemma.

**Debugging methodology that worked** (and was the only way to find the root cause):
1. Run checker with `--debug-asm-symex-first` and capture the full DAG dump to a file.
2. Grep for the unification error at the end — identifies the specific ref IDs that diverge between PHOAS and ASM sides.
3. Trace each ASM-side node back through its args recursively, by grepping `^\(\*N\*\)` in the dump. Document the shape of the nested tower.
4. Manually simulate each rewrite pass on the expanded tree, one at a time, to identify which pass fails to fire and why.
5. Fix = a single fuel-recursive rule that collapses the entire tower in one shot.

**Sharp edges to remember**:
- `reveal_node_at_least` with depth 6 fully expands the tree into nested ExprApps, so rules see the full structure at the top. But after a rule produces output, only the TOP of the output is re-matched by subsequent passes.
- `merge` is not `simplify`. `App` calls `simplify` (reveal + rewrite passes); `merge` just dedupes `(op, args)` tuples via `reverse_lookup`. If a rule output has nested ExprApps, those nested forms are merged as-is, even if they could have been simplified further.
- Adding duplicate passes to the list (e.g. `slice_set_slice_disjoint;slice_set_slice;slice_set_slice_disjoint;slice_set_slice;...`) is a cheap workaround but doesn't scale. Always prefer a recursive normalizer for alternation patterns.
- Increasing `default_node_reveal_depth` from 3 to 10 does NOT help this class of issue — reveal depth only affects initial tree expansion, not pass re-application.

## AoS layout vs SoA layout in batched specs (2026-04-07)

The batched PHOAS specs (`batched_addmod`, `batched_submod`, `batched_carry_mulmod`) use **AoS** (array-of-structures) layout: 4 complete n-limb results concatenated. For 5-limb curve25519: `[e0_l0..e0_l4, e1_l0..e1_l4, e2_l0..e2_l4, e3_l0..e3_l4]`.

This means each YMM register (4 × 64-bit lanes) processes 4 **consecutive** limbs from the flat array, which straddle element boundaries. For sub, the 0xfda balance constant (limb 0 of each element) appears at positions 0, 5, 10, 15 — rotating through YMM lanes across groups.

The n=20 trick used a completely different layout where fiat-crypto computed its own 20-limb decomposition with different bit widths and different balance constants. The proper batched specs use the same 5-limb constants as scalar, just repeated 4 times.

**Important for assembly writing**: when writing vector assembly for a batched spec, the constants and data layout follow AoS, NOT SoA. Each group of 4 consecutive limbs may span different limb positions across elements.


## peel_disjoint_set_slices won't reduce in proofs (2026-04-01)

`cbn [peel_disjoint_set_slices]`, `simpl`, `cbv`, and `unfold` all fail to reduce `peel_disjoint_set_slices lo1 s1 inner 0` to `ExprApp (slice lo1 s1, [inner])` in the base case of the induction proof, even though fuel is literally `0`. The `%N` scope on the Fixpoint or some opacity issue may be blocking reduction. `change ... with ...` was suggested but untested. Worth asking on Slack/Zulip — this is a Coq reduction behavior issue, not a math issue.


## YMM set_slice chain depth problem (2026-03-29)

When `vector_binop_idx` builds a 4-lane (YMM) result, it creates a chain:
```
set_slice 192 64 (set_slice 128 64 (set_slice 64 64 (add_lane0, add_lane1), add_lane2), add_lane3)
```

When `Store` later extracts lanes via `slice 0 64`, `slice 64 64`, etc., each `App` call runs rewrites once. With XMM (2 lanes, 1-deep chain), one pass of `slice_set_slice_disjoint` suffices. With YMM (4 lanes, 3-deep chain), `slice 0 64` needs to peel through 3 disjoint `set_slice` layers.

We added a recursive `peel_disjoint_set_slices` to handle the disjoint case (fuel=8). This fixed limb 0 extraction but limb 1 (`slice 64 64`) still fails — the non-disjoint `slice_set_slice` rule doesn't fire for unknown reasons. The recursive approach may not be the right solution; the root cause could be deeper (reveal depth, rewrite ordering, or how the Store interacts with the vector result construction).

Key DAG nodes from the failing run:
- 667 = `set_slice 64 64 [12, 666]` (base=limb0_add, val=limb1_add)
- 675 = `slice 64 64 [667]` (should simplify to `slice 0 64 [666]` via slice_set_slice, but doesn't)


## Proving peel_disjoint_set_slices correct (2026-03-31)

The `peel_disjoint_set_slices` function recursively strips disjoint `set_slice` layers from an expression before slicing. To prove `slice_set_slice_disjoint_ok`, you need a helper lemma:

```coq
Lemma peel_disjoint_set_slices_eval G d lo1 s1 inner v fuel :
  gensym_dag_ok G d ->
  eval G d (ExprApp (slice lo1 s1, [inner])) v ->
  eval G d (peel_disjoint_set_slices lo1 s1 inner fuel) v.
```

**Proof:** Induction on `fuel`.
- Base (O): returns `ExprApp (slice lo1 s1, [inner])` — exact hypothesis.
- Step (S fuel'): case split on `inner`:
  - Not `set_slice` or disjointness check fails → returns the slice expr → exact hypothesis.
  - `ExprApp (set_slice lo2 s2, [base; val])` with disjointness true:
    1. Invert `eval` on hypothesis to get `eval G d base v_base` and `eval G d val v_val`.
    2. Construct `eval G d (ExprApp (slice lo1 s1, [base])) (slice_result_of v_base)` using `EApp`.
    3. Show the Z values are equal: `slice lo1 s1 (set_slice lo2 s2 a b) = slice lo1 s1 a` when disjoint. This is a `Z.bitblast` fact.
    4. Apply IH.

The Z disjointness fact: if `lo1 + s1 <= lo2` or `lo2 + s2 <= lo1`, then:
`Z.land (Z.shiftr (Z.lor (Z.shiftl (Z.land b (Z.ones s2)) lo2) (Z.ldiff a (Z.shiftl (Z.ones s2) lo2))) lo1) (Z.ones s1) = Z.land (Z.shiftr a lo1) (Z.ones s1)`

Key `eval` facts used:
- `eval` has two constructors: `ERef` (DAG lookup) and `EApp` (direct application via `interp_op`)
- `interp_op` for `slice lo sz [a]` = `Z.land (Z.shiftr a lo) (Z.ones sz)`
- `interp_op` for `set_slice lo sz [a; b]` = `Z.lor (Z.shiftl (Z.land b (Z.ones sz)) lo) (Z.ldiff a (Z.shiftl (Z.ones sz) lo))`
- `eval_eval` gives determinism: `eval G d e v1 -> eval G d e v2 -> v1 = v2`
- The `t` tactic does initial inversion/unfolding; the helper lemma is applied after `t`.


## Load/Store decomposition (no DAG ops needed)

256-bit Load decomposes into 4x Load64 + set_slice chain (Symbolic.v:4472-4487).
256-bit Store decomposes into 4x slice + Store64 (Symbolic.v:4537-4551).
vmovdqu doesn't need a DAG-level op — it's fully handled by Load/Store decomposition.
Same pattern as 128-bit (2x Load64/Store64).


## vmovdqu/vpaddq/vzeroupper already have full YMM symex

All three were already implemented before we tried simple_avx_add_ymm.asm:
- vmovdqu: generic move, size inferred from operand (Symbolic.v:4677)
- vpaddq: SymexVectorOp auto-scales lanes (s/64), YMM = 4 lanes (Symbolic.v:4686)
- vzeroupper: loops all 16 YMM regs, slices lower 128 (Symbolic.v:4894)


## combine_consts / simp_inside

When debugging rewrite rules that "should fire but don't", check whether the
expression was created inside `combine_consts` rather than via normal `App` calls.
`combine_consts` has its own internal simplification pipeline (`simp_inside`) that
is separate from the main rewrite pass chain. If a new rewrite rule is needed inside
that pipeline, it must be added to `simp_inside` explicitly (around line 3650 in Symbolic.v).
The main rewrite passes only fire via `App` -> `simplify`, not via `merge`.