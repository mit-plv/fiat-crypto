"""Structural alignment of two DAG subgraphs.

The primary debugging question on a unification failure is: *where do these
two subtrees actually differ?*  We walk both sides simultaneously and classify
each pair of nodes as:

- ``same``     — identical op + same children (the whole subtree is equal)
- ``op-diff``  — different op_display; we stop recursing on that branch
- ``arg-diff`` — same op_display but different args (at least one pair differs)
- ``arity``    — same op but different number of children

An alignment is a tree of ``AlignNode`` records in lockstep with the two
subgraphs, so the UI can recolor each pair in a single pass.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from .parse import Dump, Node


Status = Literal["same", "op-diff", "arg-diff", "arity", "missing"]


@dataclass
class AlignNode:
    left_idx: int | None
    right_idx: int | None
    status: Status
    # When both sides resolve to real nodes we record their display strings
    # so the UI doesn't need to re-look them up.
    left_display: str = ""
    right_display: str = ""
    children: list["AlignNode"] = field(default_factory=list)


def align(
    left_dump: Dump,
    right_dump: Dump,
    left_idx: int,
    right_idx: int,
    max_depth: int = 64,
) -> AlignNode:
    """Align two subgraphs.  Typical use: ``left_dump is right_dump``.

    ``max_depth`` caps recursion at a practical limit — DAG chains in the
    equivalence checker rarely exceed ~30 deep, so 64 is safe but not huge.
    """
    return _align(left_dump, right_dump, left_idx, right_idx, max_depth)


def _align(
    ld: Dump, rd: Dump, li: int | None, ri: int | None, depth: int
) -> AlignNode:
    ln = ld.nodes.get(li) if li is not None else None
    rn = rd.nodes.get(ri) if ri is not None else None

    if ln is None and rn is None:
        return AlignNode(li, ri, "missing")
    if ln is None or rn is None:
        return AlignNode(
            li, ri, "missing",
            left_display=ln.op_display if ln else "∅",
            right_display=rn.op_display if rn else "∅",
        )

    # Same idx on both sides (common when the DAG is shared): the subtree is
    # trivially identical and we collapse it.
    if li == ri:
        return AlignNode(
            li, ri, "same",
            left_display=ln.op_display, right_display=rn.op_display,
        )

    if ln.op_display != rn.op_display:
        return AlignNode(
            li, ri, "op-diff",
            left_display=ln.op_display, right_display=rn.op_display,
        )

    if len(ln.args) != len(rn.args):
        return AlignNode(
            li, ri, "arity",
            left_display=ln.op_display, right_display=rn.op_display,
        )

    if depth <= 0:
        # Treat as same, but unexpanded — we can't tell without descending.
        return AlignNode(
            li, ri, "same",
            left_display=ln.op_display, right_display=rn.op_display,
        )

    children = [
        _align(ld, rd, lc, rc, depth - 1)
        for lc, rc in zip(ln.args, rn.args)
    ]
    # Propagate diff status upward: if any child disagrees, this node is
    # "arg-diff"; otherwise "same".
    status: Status = "same"
    for c in children:
        if c.status != "same":
            status = "arg-diff"
            break
    return AlignNode(
        li, ri, status,
        left_display=ln.op_display, right_display=rn.op_display,
        children=children,
    )


def first_divergence(root: AlignNode) -> AlignNode | None:
    """Return the topmost node whose status isn't ``same`` — usually the
    most informative place to start an interactive exploration."""
    if root.status == "same":
        return None
    # Descend into arg-diff nodes until we hit a real op-diff / arity / leaf.
    node = root
    while node.status == "arg-diff":
        diffing = [c for c in node.children if c.status != "same"]
        if len(diffing) != 1:
            return node
        node = diffing[0]
    return node
