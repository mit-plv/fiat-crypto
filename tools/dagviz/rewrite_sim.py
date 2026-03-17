"""Best-effort simulation of Symbolic.v rewrite rules on a parsed dump.

This is a debugging aid, not a faithful replica of Rocq's rewriter.  When the
user hits ``?`` in the TUI, we try each of the rules we *know how to apply*
against the cursor node and report which ones fire (and what they would
produce).  The output is purely informational — we do not mutate the dump.

The rules implemented here are the SIMD-focused ones the user cares about:

- ``slice_slice``
- ``slice_set_slice``
- ``slice_set_slice_disjoint``
- ``slice_tower`` (the fuel-recursive normalizer from 2026-04-11)

If this diverges from the Rocq rules, it is a *bug in this file*, not in
Symbolic.v.  Keep this file small and paired with the Coq source so drift is
easy to spot.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from .parse import Dump, Node


@dataclass
class RuleReport:
    rule: str
    fired: bool
    detail: str


def simulate_rewrites(dump: Dump, idx: int) -> str:
    node = dump.nodes.get(idx)
    if node is None:
        return f"#{idx} not in dump"
    reports = [
        _slice_slice(dump, node),
        _slice_set_slice(dump, node),
        _slice_set_slice_disjoint(dump, node),
        _slice_tower(dump, node),
    ]
    lines = [f"simulate rewrites on #{idx}  {node.op_display}"]
    for r in reports:
        marker = "✓" if r.fired else " "
        lines.append(f"  [{marker}] {r.rule:28s} {r.detail}")
    return "\n".join(lines)


# --- helpers ---

def _is(node: Node, name: str) -> bool:
    return node.op_name == name


def _int_params(node: Node) -> list[int]:
    out = []
    for p in node.op_params:
        try:
            out.append(int(p))
        except ValueError:
            return []
    return out


# --- rules ---

def _slice_slice(dump: Dump, node: Node) -> RuleReport:
    if not _is(node, "slice") or len(node.args) != 1:
        return RuleReport("slice_slice", False, "outer not slice/1")
    outer = _int_params(node)
    if len(outer) != 2:
        return RuleReport("slice_slice", False, "outer params unparsed")
    lo1, s1 = outer
    inner = dump.nodes.get(node.args[0])
    if inner is None or not _is(inner, "slice") or len(inner.args) != 1:
        return RuleReport("slice_slice", False, "inner not slice/1")
    inner_p = _int_params(inner)
    if len(inner_p) != 2:
        return RuleReport("slice_slice", False, "inner params unparsed")
    lo2, s2 = inner_p
    if lo1 + s1 <= s2:
        return RuleReport(
            "slice_slice", True,
            f"→ slice {lo2+lo1} {s1} [#{inner.args[0]}]",
        )
    return RuleReport("slice_slice", False, f"lo1+s1={lo1+s1} > s2={s2}")


def _slice_set_slice(dump: Dump, node: Node) -> RuleReport:
    if not _is(node, "slice") or len(node.args) != 1:
        return RuleReport("slice_set_slice", False, "outer not slice/1")
    outer = _int_params(node)
    if len(outer) != 2:
        return RuleReport("slice_set_slice", False, "outer params unparsed")
    lo1, s1 = outer
    inner = dump.nodes.get(node.args[0])
    if inner is None or not _is(inner, "set_slice") or len(inner.args) != 2:
        return RuleReport("slice_set_slice", False, "inner not set_slice/2")
    p = _int_params(inner)
    if len(p) != 2:
        return RuleReport("slice_set_slice", False, "inner params unparsed")
    lo2, s2 = p
    # Contained case: slice range falls entirely inside set_slice range.
    if lo2 <= lo1 and lo1 + s1 <= lo2 + s2:
        return RuleReport(
            "slice_set_slice", True,
            f"→ slice {lo1-lo2} {s1} [#{inner.args[1]}]",
        )
    return RuleReport(
        "slice_set_slice", False,
        f"slice [{lo1},{lo1+s1}) not ⊆ set_slice [{lo2},{lo2+s2})",
    )


def _slice_set_slice_disjoint(dump: Dump, node: Node) -> RuleReport:
    if not _is(node, "slice") or len(node.args) != 1:
        return RuleReport("slice_set_slice_disjoint", False, "outer not slice/1")
    outer = _int_params(node)
    if len(outer) != 2:
        return RuleReport("slice_set_slice_disjoint", False, "outer params unparsed")
    lo1, s1 = outer
    inner = dump.nodes.get(node.args[0])
    if inner is None or not _is(inner, "set_slice") or len(inner.args) != 2:
        return RuleReport("slice_set_slice_disjoint", False, "inner not set_slice/2")
    p = _int_params(inner)
    if len(p) != 2:
        return RuleReport("slice_set_slice_disjoint", False, "inner params unparsed")
    lo2, s2 = p
    if lo1 + s1 <= lo2 or lo2 + s2 <= lo1:
        return RuleReport(
            "slice_set_slice_disjoint", True,
            f"→ slice {lo1} {s1} [#{inner.args[0]}]",
        )
    return RuleReport(
        "slice_set_slice_disjoint", False,
        f"[{lo1},{lo1+s1}) overlaps [{lo2},{lo2+s2})",
    )


def _slice_tower(dump: Dump, node: Node) -> RuleReport:
    """Iterated descent through nested slice/set_slice layers, mirroring
    the fuel-recursive ``slice_tower_normalize`` Fixpoint in Symbolic.v."""
    if not _is(node, "slice") or len(node.args) != 1:
        return RuleReport("slice_tower", False, "outer not slice/1")
    outer = _int_params(node)
    if len(outer) != 2:
        return RuleReport("slice_tower", False, "outer params unparsed")
    lo, sz = outer
    path: list[str] = []
    cur_idx = node.args[0]
    fuel = 16
    while fuel > 0:
        inner = dump.nodes.get(cur_idx)
        if inner is None:
            return RuleReport(
                "slice_tower",
                len(path) > 0,
                f"stops at #{cur_idx} <missing>  path: {' → '.join(path)}",
            )
        if _is(inner, "slice") and len(inner.args) == 1:
            p = _int_params(inner)
            if len(p) != 2:
                break
            lo2, s2 = p
            if lo + sz <= s2:
                path.append(f"peel slice→ lo={lo2+lo}")
                lo = lo2 + lo
                cur_idx = inner.args[0]
                fuel -= 1
                continue
            break
        if _is(inner, "set_slice") and len(inner.args) == 2:
            p = _int_params(inner)
            if len(p) != 2:
                break
            lo2, s2 = p
            if lo + sz <= lo2 or lo2 + s2 <= lo:
                path.append(f"disjoint set_slice→ base #{inner.args[0]}")
                cur_idx = inner.args[0]
                fuel -= 1
                continue
            if lo2 <= lo and lo + sz <= lo2 + s2:
                new_lo = lo - lo2
                path.append(f"contained set_slice→ val #{inner.args[1]} lo={new_lo}")
                lo = new_lo
                cur_idx = inner.args[1]
                fuel -= 1
                continue
            break
        break
    final = dump.nodes.get(cur_idx)
    final_repr = f"#{cur_idx}" + (f" ({final.op_display})" if final else "")
    if path:
        return RuleReport(
            "slice_tower",
            True,
            f"→ slice {lo} {sz} [{final_repr}]  via {len(path)} layers:"
            + "\n        " + "\n        ".join(path),
        )
    return RuleReport("slice_tower", False, "no layers matched")
