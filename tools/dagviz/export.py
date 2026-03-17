"""Graphviz export for dagviz.

When the TUI isn't enough — e.g. you want to paste a diagram into notes or
share it with a collaborator — dump a subgraph to a ``.dot`` file and run
``dot -Tsvg`` on it externally. We keep this deliberately minimal: no
clustering, no colours, just ``idx -> idx`` edges labelled with child order.
"""

from __future__ import annotations

from .parse import Dump


def to_dot(dump: Dump, root: int, max_depth: int = 8, name: str = "dag") -> str:
    lines = [f'digraph {name} {{', '  rankdir=TB;', '  node [shape=box, fontname="monospace"];']
    seen: set[int] = set()
    _walk(dump, root, max_depth, seen, lines)
    lines.append("}")
    return "\n".join(lines)


def _walk(dump: Dump, idx: int, depth: int, seen: set[int], lines: list[str]) -> None:
    if idx in seen:
        return
    seen.add(idx)
    node = dump.nodes.get(idx)
    if node is None:
        lines.append(f'  n{idx} [label="#{idx} <missing>", color=red];')
        return
    label = f"#{idx}\\n{node.op_display}"
    lines.append(f'  n{idx} [label="{label}"];')
    if depth <= 0 and node.args:
        lines.append(f'  n{idx}_stub [label="…{len(node.args)}", shape=plaintext];')
        lines.append(f"  n{idx} -> n{idx}_stub;")
        return
    for i, c in enumerate(node.args):
        _walk(dump, c, depth - 1, seen, lines)
        lines.append(f'  n{idx} -> n{c} [label="{i}"];')
