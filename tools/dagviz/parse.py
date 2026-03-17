"""Parser for Rocq equivalence checker dumps.

The dump format produced on a failed equivalence check contains:

1. A DAG body between ``(*dag*)[`` and a matching ``]``, with entries of the form

   ``(*IDX*) (OP_STR, [ARG1, ARG2, ...]);  (*ANNOTATION*)``

2. A ``symbolic_reg_state`` line: ``[(REG, IDX), ...]``.
3. A ``symbolic_flag_state`` line (ignored for now).
4. A ``symbolic_mem_state`` block (ignored for now).
5. A unification error section starting with ``Unable to unify:`` that contains:
   - a top line with the two output index lists:
     ``Unable to unify: [inr [asm_idxs...]] == [inr [phoas_idxs...]]``
   - a divergence walk: alternating ``index N: #A ≠ #B`` / ``(op, args) ≠ (op, args)``
     lines that step down to the first real mismatch.

This parser is deliberately forgiving: it works on the existing human-pretty
output rather than requiring a machine format.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re
from typing import Iterable


# --- Node model -------------------------------------------------------------

@dataclass
class Node:
    idx: int
    op_name: str              # e.g. "slice", "set_slice", "vadd", "add", "old"
    op_params: tuple[str, ...]  # e.g. ("0", "64") for slice 0 64
    args: tuple[int, ...]     # child DAG indices
    annotation: str | None = None  # trailing (* ... *) comment, if any
    raw_op: str = ""          # original op string, for display

    @property
    def op_display(self) -> str:
        if self.op_params:
            return f"{self.op_name} {' '.join(self.op_params)}"
        return self.op_name

    @property
    def sexp_head(self) -> str:
        return f"({self.op_display})" if not self.args else f"({self.op_display}"


@dataclass
class RegBinding:
    reg: str
    idx: int


@dataclass
class MismatchEntry:
    """One step of the divergence walk.

    ``left_idx`` is the ASM-side idx; ``right_idx`` is the PHOAS-side idx.
    ``left_repr``/``right_repr`` hold the pretty-printed op+args lines the
    dumper emitted right after the ``index N: #A ≠ #B`` line (may be ``None``
    if the dumper stopped at a leaf).
    """
    depth: int
    left_idx: int
    right_idx: int
    left_repr: str | None = None
    right_repr: str | None = None


@dataclass
class Dump:
    nodes: dict[int, Node] = field(default_factory=dict)
    reg_history: list[RegBinding] = field(default_factory=list)
    asm_output_roots: list[int] = field(default_factory=list)
    phoas_output_roots: list[int] = field(default_factory=list)
    divergence: list[MismatchEntry] = field(default_factory=list)
    # Optional top-level mismatch summary (the final op-mismatch line)
    final_mismatch: str | None = None

    # --- helpers ---

    def latest_reg_value(self, reg: str) -> int | None:
        """Return the last-bound idx for ``reg``, or None if never bound."""
        for b in reversed(self.reg_history):
            if b.reg == reg:
                return b.idx
        return None

    def final_reg_state(self) -> dict[str, int]:
        """Build the final register state by walking reg_history in order."""
        out: dict[str, int] = {}
        for b in self.reg_history:
            out[b.reg] = b.idx
        return out

    def get(self, idx: int) -> Node | None:
        return self.nodes.get(idx)

    def children(self, idx: int) -> Iterable[int]:
        node = self.nodes.get(idx)
        if node is None:
            return ()
        return node.args

    def reachable(self, root: int, max_depth: int | None = None) -> set[int]:
        """BFS downward from ``root``; returns the set of reachable idxs."""
        seen: set[int] = set()
        frontier: list[tuple[int, int]] = [(root, 0)]
        while frontier:
            idx, depth = frontier.pop()
            if idx in seen:
                continue
            if idx not in self.nodes:
                continue
            seen.add(idx)
            if max_depth is not None and depth >= max_depth:
                continue
            for c in self.nodes[idx].args:
                if c not in seen:
                    frontier.append((c, depth + 1))
        return seen


# --- Regexes ---------------------------------------------------------------

# (*IDX*)(WS)(OP_AND_ARGS);(OPTIONAL_TRAILING_COMMENT)
# We capture the node body between the first '(' after the idx marker and the
# matching `);`, then post-process.  Using a single monolithic regex for the
# whole line is brittle because op strings vary a lot; instead we split.
_NODE_LINE = re.compile(
    r"""
    ^\s*
    \(\*(?P<idx>\d+)\*\)      # (*IDX*)
    \s+
    \((?P<body>.*)\);         # (body);
    (?:\s*\(\*(?P<anno>.+?)\*\))?   # optional trailing (*annotation*)
    \s*$
    """,
    re.VERBOSE,
)

# Inside the body, split into op_str and args_str at the first ", [".
_BODY_SPLIT = re.compile(r",\s*\[(?P<args>[^\]]*)\]$")

# Register binding: (REG, IDX).  Reg is a lowercase identifier.
_REG_ENTRY = re.compile(r"\((?P<reg>[a-z][a-z0-9]*),\s*(?P<idx>\d+)\)")

# Top-level unification line:
# Unable to unify: [inr [ids...]] == [inr [ids...]]
_UNIFY_TOP = re.compile(
    r"^Unable to unify:\s*\[inr\s*\[(?P<left>[\d,\s]*)\]\]\s*==\s*\[inr\s*\[(?P<right>[\d,\s]*)\]\]"
)

# index N: #A ≠ #B
_INDEX_WALK = re.compile(
    r"^index\s+(?P<depth>\d+):\s*#(?P<left>\d+)\s*(?:≠|!=|<>)\s*#(?P<right>\d+)"
)

# (op, args) ≠ (op, args) — the pretty-printed mismatch lines that the
# dumper emits beneath each index line.  We capture everything, we don't
# try to parse the two sides individually.
_MISMATCH_REPR = re.compile(r"^\((?P<left>.+?)\)\s*(?:≠|!=|<>)\s*\((?P<right>.+?)\)\s*$")


# --- Public API ------------------------------------------------------------

def parse_file(path: str | Path) -> Dump:
    """Parse a dump file and return a populated ``Dump``."""
    text = Path(path).read_text(errors="replace")
    return parse_text(text)


def parse_text(text: str) -> Dump:
    dump = Dump()
    lines = text.splitlines()

    # We make a single pass over the lines, tracking state by section.
    in_dag = False
    for i, line in enumerate(lines):
        if not in_dag:
            if "(*dag*)[" in line:
                in_dag = True
            continue

        # Stop the DAG block at the closing bracket on its own line.
        stripped = line.strip()
        if stripped == "]" or stripped == "];":
            in_dag = False
            continue

        node = _parse_node_line(line)
        if node is not None:
            dump.nodes[node.idx] = node

    # Post-DAG sections — scan the remainder for reg state, unification, etc.
    for i, line in enumerate(lines):
        if line.lstrip().startswith("symbolic_reg_state"):
            _parse_reg_state_line(line, dump)
        elif line.startswith("Unable to unify:"):
            m = _UNIFY_TOP.match(line)
            if m:
                dump.asm_output_roots = _parse_int_list(m.group("left"))
                dump.phoas_output_roots = _parse_int_list(m.group("right"))

    # Divergence walk: a sequence of "index N: #A ≠ #B" lines each optionally
    # followed by a "(op,...) ≠ (op,...)" pretty representation.
    _parse_divergence_walk(lines, dump)
    return dump


# --- Internal helpers ------------------------------------------------------

def _parse_node_line(line: str) -> Node | None:
    m = _NODE_LINE.match(line)
    if m is None:
        return None
    idx = int(m.group("idx"))
    body = m.group("body")
    anno = m.group("anno")
    sm = _BODY_SPLIT.search(body)
    if sm is None:
        return None
    args_str = sm.group("args")
    op_str = body[: sm.start()].rstrip()
    op_name, op_params = _split_op(op_str)
    args = tuple(int(x) for x in args_str.replace(",", " ").split() if x)
    return Node(
        idx=idx,
        op_name=op_name,
        op_params=op_params,
        args=args,
        annotation=anno,
        raw_op=op_str,
    )


def _split_op(op_str: str) -> tuple[str, tuple[str, ...]]:
    """Split an op string into ``(name, params)``.

    Handles the odd cases: ``vadd 64x4`` → ("vadd", ("64", "4")), ``old 64 7`` →
    ("old", ("64", "7")), ``const 119...`` → ("const", ("119...",)).
    """
    op_str = op_str.strip()
    if not op_str:
        return ("", ())
    tokens = op_str.split()
    name = tokens[0]
    rest = tokens[1:]
    # Special case: vadd/vsub use "LWxNL" format.
    if name in ("vadd", "vsub") and len(rest) == 1 and "x" in rest[0]:
        lw, _, nl = rest[0].partition("x")
        return (name, (lw, nl))
    return (name, tuple(rest))


def _parse_reg_state_line(line: str, dump: Dump) -> None:
    # The reg state is written as: symbolic_reg_state := [(rax, 123), ...];
    for m in _REG_ENTRY.finditer(line):
        dump.reg_history.append(RegBinding(reg=m.group("reg"), idx=int(m.group("idx"))))


def _parse_int_list(s: str) -> list[int]:
    return [int(x) for x in s.replace(",", " ").split() if x]


def _parse_divergence_walk(lines: list[str], dump: Dump) -> None:
    i = 0
    n = len(lines)
    while i < n:
        m = _INDEX_WALK.match(lines[i])
        if m is None:
            # Also capture the tail "Operation mismatch:" line if present.
            if lines[i].startswith("Operation mismatch:"):
                dump.final_mismatch = lines[i].strip()
            i += 1
            continue
        entry = MismatchEntry(
            depth=int(m.group("depth")),
            left_idx=int(m.group("left")),
            right_idx=int(m.group("right")),
        )
        # Optionally consume the next line if it's a "(...)≠(...)" repr.
        if i + 1 < n:
            mm = _MISMATCH_REPR.match(lines[i + 1].strip())
            if mm:
                entry.left_repr = mm.group("left").strip()
                entry.right_repr = mm.group("right").strip()
                i += 1
        dump.divergence.append(entry)
        i += 1
