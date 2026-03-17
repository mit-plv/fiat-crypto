"""Text rendering of DAG subgraphs rooted at a given idx.

The ``trace`` subcommand is the simplest useful view: given a dump and an idx,
print an indented s-expression tree of everything reachable from that idx down
to a max depth, with optional sharing (shared subtrees shown once and then
referenced by idx).
"""

from __future__ import annotations

from .parse import Dump, Node


def render_tree(
    dump: Dump,
    root: int,
    max_depth: int = 6,
    share: bool = True,
) -> str:
    """Render the subgraph under ``root`` as an indented s-expression.

    ``share=True``: any idx that appears more than once in the reachable set
    is printed in full at its first occurrence and replaced with ``#idx`` on
    subsequent visits. This keeps the output compact for DAGs (as opposed to
    trees) without hiding structure.
    """
    # Count references so we can decide which nodes are "shared".
    refcount: dict[int, int] = {}
    _count_refs(dump, root, max_depth, refcount)
    shared: set[int] = {i for i, c in refcount.items() if c > 1} if share else set()
    printed: set[int] = set()
    lines: list[str] = []
    _render(dump, root, 0, max_depth, shared, printed, lines)
    return "\n".join(lines)


def _count_refs(
    dump: Dump, idx: int, depth: int, refcount: dict[int, int]
) -> None:
    refcount[idx] = refcount.get(idx, 0) + 1
    if refcount[idx] > 1:
        return
    if depth <= 0:
        return
    node = dump.nodes.get(idx)
    if node is None:
        return
    for c in node.args:
        _count_refs(dump, c, depth - 1, refcount)


def _render(
    dump: Dump,
    idx: int,
    indent: int,
    depth: int,
    shared: set[int],
    printed: set[int],
    lines: list[str],
) -> None:
    pad = "  " * indent
    node = dump.nodes.get(idx)
    if node is None:
        lines.append(f"{pad}#{idx} <missing>")
        return
    # If this idx has been printed already and is shared, emit a back-ref.
    if idx in printed and idx in shared:
        lines.append(f"{pad}#{idx} -> {node.op_display}")
        return
    printed.add(idx)

    head = f"#{idx} ({node.op_display}"
    if not node.args:
        lines.append(f"{pad}{head})")
        return
    if depth <= 0:
        lines.append(f"{pad}{head} …{len(node.args)} children)")
        return
    lines.append(f"{pad}{head}")
    for c in node.args:
        _render(dump, c, indent + 1, depth - 1, shared, printed, lines)
    lines.append(f"{pad})")


def render_divergence_summary(dump: Dump) -> str:
    """Concise summary of the divergence walk for quick triage."""
    out: list[str] = []
    out.append(f"ASM  roots: {dump.asm_output_roots}")
    out.append(f"PHOAS roots: {dump.phoas_output_roots}")
    out.append("")
    out.append(f"Divergence walk ({len(dump.divergence)} steps):")
    for i, e in enumerate(dump.divergence):
        out.append(
            f"  [{i}] depth={e.depth}  #{e.left_idx}  ≠  #{e.right_idx}"
        )
        if e.left_repr:
            out.append(f"        L: ({e.left_repr})")
        if e.right_repr:
            out.append(f"        R: ({e.right_repr})")
    if dump.final_mismatch:
        out.append("")
        out.append(dump.final_mismatch)
    return "\n".join(out)
