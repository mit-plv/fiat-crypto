"""Shape hashing for clustering identical subtrees.

Two DAG subtrees have the same *shape* when the tree of ``op_display`` strings
and the recursive shapes of their children match.  Leaf idxs are deliberately
ignored so that, for example, two ``(add 64 (const _) (const _))`` trees
against different constants hash the same.  This lets the UI fold
boilerplate away and surface structural diversity.
"""

from __future__ import annotations

from .parse import Dump


def shape_hash(dump: Dump, idx: int, max_depth: int = 8) -> str:
    """Hash by structure, not by idx or leaf values."""
    cache: dict[int, str] = {}
    return _shape(dump, idx, max_depth, cache)


def _shape(dump: Dump, idx: int, depth: int, cache: dict[int, str]) -> str:
    if idx in cache:
        return cache[idx]
    n = dump.nodes.get(idx)
    if n is None:
        cache[idx] = "∅"
        return "∅"
    # Constants and "old" nodes are leaves that differ only in value; hash
    # them by op name only so that unrelated old/const values cluster.
    if n.op_name in ("const", "old") and not n.args:
        h = f"<{n.op_name}>"
        cache[idx] = h
        return h
    if depth <= 0:
        h = f"({n.op_display}…)"
        cache[idx] = h
        return h
    kids = [_shape(dump, c, depth - 1, cache) for c in n.args]
    h = f"({n.op_display} {' '.join(kids)})" if kids else f"({n.op_display})"
    cache[idx] = h
    return h
