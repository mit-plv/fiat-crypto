# dagviz — DAG debugging for the fiat-crypto equivalence checker

Personal tool for inspecting the DAG dumps the equivalence checker produces
when a `--hints-file` run fails. Primary goal: make unification failures
easy to walk through by hand.

## Installing

```sh
pip install textual rich
```

(Also listed in `tools/dagviz/requirements.txt`.)

## Getting a dump

Run the checker with `--debug-asm-symex-first` and redirect to a file. Example:

```sh
./src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
    25519 64 '(auto)' '2^255 - 19' batch_carry \
    --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 \
    --debug-asm-symex-first \
    --hints-file test-asm/batch_avx_carry.asm \
    -o /dev/null --output-asm /dev/null 2>&1 | tee /tmp/mydump.txt
```

The dump contains three sections the parser cares about:
1. A `(*dag*)[` block listing every DAG node with idx, op, and arg idxs.
2. A `symbolic_reg_state` line mapping register names to idxs.
3. An `Unable to unify: [inr [..]] == [inr [..]]` section followed by a
   divergence walk (`index N: #A ≠ #B` lines alternating with pretty-printed
   op/arg diffs).

The tool is forgiving — it ignores everything else.

## Subcommands

All invoked as `python -m tools.dagviz <cmd> <dump> [options]`.

### `stats DUMP`

Quick sanity check: node count, histogram of ops, divergence length.

```sh
python -m tools.dagviz stats /tmp/mydump.txt
```

### `diverge DUMP`

Print the full divergence walk in one place:

```sh
python -m tools.dagviz diverge /tmp/mydump.txt
```

Shows each `#A ≠ #B` step with the op-level mismatch line that follows it
in the checker output, plus the final `Operation mismatch:` summary. This
is usually the first thing to look at.

### `trace DUMP --idx N [--depth D]`

Print the subgraph rooted at idx `N` as an indented s-expression. Repeated
subtrees are printed once and then back-referenced by `#idx`:

```sh
python -m tools.dagviz trace /tmp/mydump.txt --idx 820 --depth 4
```

Defaults: `--depth 6`, sharing enabled. Pass `--no-share` to always expand
shared subtrees in full (useful when you want a pure tree view).

### `dot DUMP --idx N [--depth D]`

Graphviz export. Render with `dot -Tsvg` or `dot -Tpng`:

```sh
python -m tools.dagviz dot /tmp/mydump.txt --idx 820 --depth 4 > /tmp/dag.dot
dot -Tsvg /tmp/dag.dot > /tmp/dag.svg
```

### `tui DUMP`

Interactive Textual viewer — the main event. Opens with the first
divergence step loaded, ASM side on the left and PHOAS side on the right.

```sh
python -m tools.dagviz tui /tmp/mydump.txt
```

**Keys:**

| Key | Action |
|---|---|
| `n` / `p` | next / previous divergence step |
| `j` / `k` | cursor down / up |
| `l`       | expand current node (or move down if already expanded) |
| `h`       | collapse current node (or move to parent) |
| `f`       | toggle follow mode — mirror cursor in the opposite tree |
| `c`       | cluster by shape hash (reports unique shapes for now) |
| `g`       | goto idx (prompt, jumps left tree to an arbitrary idx) |
| `?`       | simulate rewrite rules on the cursor — prints which rules would fire |
| `q`       | quit |

The alignment algorithm colours each node by status:

- **dim** — matching subtree
- **yellow** — same op but children differ (arg-diff)
- **bold red** — different op or arity (op-diff / arity)

Colouring propagates upward: any arg-diff node turns yellow too, so you can
scan the tree top-down until you hit the first red leaf.

## What the tool is for

One very specific workflow:

1. A `--hints-file` run fails with `Unable to unify:`.
2. Capture the dump.
3. `python -m tools.dagviz tui DUMP`.
4. Step through divergences with `n`, read off the op mismatch at the
   bottom of each step, and walk down the yellow trail with `j`/`l`.
5. When you hit a `slice`/`set_slice` tower, hit `?` — the rewrite
   simulator tells you whether `slice_slice`, `slice_set_slice`,
   `slice_set_slice_disjoint`, or `slice_tower` should have collapsed the
   pattern and why. If they should have fired but didn't, something is
   wrong in the Rocq rewriter.

This is what we used to diagnose the `batch_avx_carry` failure that led to
the `slice_tower` rewrite rule (see NOTES.md 2026-04-11).

## Caveats

- The rewrite simulator in `rewrite_sim.py` is a best-effort Python
  translation of a subset of the Rocq rules. If Symbolic.v and rewrite_sim
  disagree on whether a rule fires, **the bug is in rewrite_sim.py**, not
  in Symbolic.v. Keep them in sync manually.
- The parser expects the exact human-pretty dump format. If the dump
  format changes, `parse.py` regexes need updating.
- The `cluster` action currently only reports unique shape counts — it
  doesn't collapse identical subtrees in the TUI yet.
- The tool is single-dump. Cross-run diffs aren't supported.
