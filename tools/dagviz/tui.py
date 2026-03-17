"""Interactive TUI for exploring DAG unification failures.

Layout:

    ┌─────────────── divergence walk (footer key: n/p) ────────────────┐
    │                                                                   │
    ├───────────── left (ASM) ──────────┬───────── right (PHOAS) ───────┤
    │  #820 add 64                      │  #1056 add 64                 │
    │    #810 shr 64         [DIFF]     │    #15 old 64 15    [DIFF]   │
    │    #819 slice 0 64                │    #1054 slice 0 64           │
    │                                   │                               │
    ├──────────────── detail pane (node metadata, annotation) ──────────┤
    └───────────────────────────────────────────────────────────────────┘

Keys:
  n / p : next / previous divergence step
  j / k : move cursor down / up
  l     : expand cursor (or descend into child if already expanded)
  h     : collapse / ascend
  enter : toggle expand
  f     : follow mode (when cursor moves on left, right auto-aligns)
  c     : cluster — collapse subtrees with identical shape hashes
  g     : goto idx (prompt)
  ?     : simulate rewrite rules on the cursor (best-effort)
  q     : quit
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable

from rich.text import Text
from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import Horizontal, Vertical
from textual.reactive import reactive
from textual.screen import ModalScreen
from textual.widgets import Footer, Header, Input, Static, Tree
from textual.widgets.tree import TreeNode

from .align import AlignNode, align, first_divergence
from .parse import Dump, Node, parse_file
from .reduce import shape_hash
from .rewrite_sim import simulate_rewrites


# ---- Data model for a mutable per-side tree ------------------------------


@dataclass
class TreeEntry:
    """Payload attached to each Textual TreeNode.

    Stores the DAG idx plus the *aligned* node (if any). The alignment status
    drives colouring — we recolour at render time rather than caching styled
    labels because the same idx can appear under different alignment contexts
    (e.g. when the user changes divergence steps).
    """
    idx: int
    side: str                     # "L" or "R"
    align: AlignNode | None = None
    depth_hint: int = 0           # for repr/debug only


# ---- Mismatch clusters ---------------------------------------------------


def cluster_shapes(dump: Dump, root: int, max_depth: int = 8) -> dict[int, str]:
    """Build ``idx -> shape hash`` for every node reachable from ``root``."""
    out: dict[int, str] = {}
    _shape(dump, root, max_depth, out)
    return out


def _shape(dump: Dump, idx: int, depth: int, cache: dict[int, str]) -> str:
    if idx in cache:
        return cache[idx]
    n = dump.nodes.get(idx)
    if n is None:
        cache[idx] = "∅"
        return "∅"
    if depth <= 0:
        h = f"({n.op_display} …)"
        cache[idx] = h
        return h
    kids = [_shape(dump, c, depth - 1, cache) for c in n.args]
    h = f"({n.op_display} {' '.join(kids)})" if kids else f"({n.op_display})"
    cache[idx] = h
    return h


# ---- Widgets -------------------------------------------------------------


class SideTree(Tree[TreeEntry]):
    """A ``Tree`` widget that lazy-loads DAG children on expand.

    Each node stores a ``TreeEntry``.  When the user expands it, we look up
    the DAG node and populate its children.  This keeps the initial render
    cheap even on huge DAGs.
    """

    BINDINGS = [
        Binding("l", "descend", "descend"),
        Binding("h", "ascend", "ascend"),
    ]

    def __init__(self, side: str, dump: Dump, **kw) -> None:
        super().__init__("", **kw)
        self.side = side
        self.dump = dump
        self.show_root = True
        self.guide_depth = 2

    def mount_root(self, idx: int, align_node: AlignNode | None) -> None:
        self.clear()
        entry = TreeEntry(idx=idx, side=self.side, align=align_node)
        self.root.data = entry
        self.root.set_label(self._label_for(entry))
        self._populate(self.root)
        self.root.expand()

    # --- label rendering ---

    def _label_for(self, entry: TreeEntry) -> Text:
        node = self.dump.nodes.get(entry.idx)
        if node is None:
            return Text(f"#{entry.idx} <missing>", style="red")
        status = entry.align.status if entry.align else "same"
        style_map = {
            "same": "dim",
            "arg-diff": "yellow",
            "op-diff": "bold red",
            "arity": "bold red",
            "missing": "red",
        }
        style = style_map.get(status, "white")
        label = Text()
        label.append(f"#{entry.idx} ", style="cyan")
        label.append(node.op_display, style=style)
        if node.args:
            label.append(f"  ({len(node.args)})", style="grey50")
        if node.annotation:
            label.append(f"  ; {node.annotation[:40]}", style="grey30")
        return label

    def _populate(self, tn: TreeNode[TreeEntry]) -> None:
        if tn.children:
            return
        entry = tn.data
        assert entry is not None
        node = self.dump.nodes.get(entry.idx)
        if node is None:
            return
        align_children: list[AlignNode | None]
        if entry.align is not None and entry.align.children:
            align_children = list(entry.align.children)
        else:
            align_children = [None] * len(node.args)
        for child_idx, child_align in zip(node.args, align_children):
            child_entry = TreeEntry(
                idx=child_idx, side=self.side, align=child_align,
                depth_hint=entry.depth_hint + 1,
            )
            child_node = tn.add(self._label_for(child_entry), data=child_entry, expand=False)
            # Leaves still get an explicit "no children" state.
            if not self.dump.nodes.get(child_idx, Node(0, "", (), ())).args:
                child_node.allow_expand = False

    def on_tree_node_expanded(self, event: Tree.NodeExpanded) -> None:
        self._populate(event.node)

    def action_descend(self) -> None:
        node = self.cursor_node
        if node is None:
            return
        if not node.is_expanded:
            node.expand()
        elif node.children:
            self.action_cursor_down()

    def action_ascend(self) -> None:
        node = self.cursor_node
        if node is None:
            return
        if node.is_expanded and node.children:
            node.collapse()
        elif node.parent is not None:
            self.move_cursor(node.parent)


# ---- Modal: goto idx -----------------------------------------------------


class GotoScreen(ModalScreen[int | None]):
    def compose(self) -> ComposeResult:
        yield Input(placeholder="go to idx (e.g. 820)", id="goto-input")

    def on_input_submitted(self, event: Input.Submitted) -> None:
        try:
            self.dismiss(int(event.value))
        except ValueError:
            self.dismiss(None)


# ---- Main app ------------------------------------------------------------


class DagVizApp(App):
    CSS = """
    Screen { layout: vertical; }
    #walk { height: auto; padding: 0 1; background: $panel; color: $text; }
    #body { height: 1fr; }
    .pane { width: 1fr; border: round $primary; }
    #detail { height: 10; border: round $accent; padding: 0 1; }
    """

    BINDINGS = [
        Binding("q", "quit", "quit"),
        Binding("n", "next_div", "next ≠"),
        Binding("p", "prev_div", "prev ≠"),
        Binding("j", "cursor_down", "↓"),
        Binding("k", "cursor_up", "↑"),
        Binding("f", "toggle_follow", "follow"),
        Binding("c", "cluster", "cluster"),
        Binding("g", "goto", "goto"),
        Binding("question_mark", "simulate", "simulate rewrites"),
    ]

    divergence_cursor: reactive[int] = reactive(0)
    follow_mode: reactive[bool] = reactive(True)

    def __init__(self, dump: Dump) -> None:
        super().__init__()
        self.dump = dump

    def compose(self) -> ComposeResult:
        yield Header()
        yield Static(self._walk_label(), id="walk")
        with Horizontal(id="body"):
            self.left = SideTree("L", self.dump, id="left", classes="pane")
            self.right = SideTree("R", self.dump, id="right", classes="pane")
            yield self.left
            yield self.right
        yield Static("", id="detail")
        yield Footer()

    def on_mount(self) -> None:
        self._jump_to(0)
        self.left.focus()

    # --- divergence stepping ---

    def _walk_label(self) -> str:
        if not self.dump.divergence:
            return "(no divergence walk in dump)"
        idx = self.divergence_cursor
        e = self.dump.divergence[idx]
        arrow = f"step {idx+1}/{len(self.dump.divergence)}"
        return f"{arrow}  depth={e.depth}  L #{e.left_idx}  ≠  R #{e.right_idx}   (n/p to step, f={self.follow_mode})"

    def _jump_to(self, step: int) -> None:
        if not self.dump.divergence:
            return
        step = max(0, min(step, len(self.dump.divergence) - 1))
        self.divergence_cursor = step
        e = self.dump.divergence[step]
        alignment = align(self.dump, self.dump, e.left_idx, e.right_idx, max_depth=64)
        self.left.mount_root(e.left_idx, alignment)
        self.right.mount_root(e.right_idx, alignment)
        self.query_one("#walk", Static).update(self._walk_label())
        self._update_detail()

    def action_next_div(self) -> None:
        self._jump_to(self.divergence_cursor + 1)

    def action_prev_div(self) -> None:
        self._jump_to(self.divergence_cursor - 1)

    def action_cursor_down(self) -> None:
        self.focused_tree().action_cursor_down() if self.focused_tree() else None
        self._sync_follow()
        self._update_detail()

    def action_cursor_up(self) -> None:
        self.focused_tree().action_cursor_up() if self.focused_tree() else None
        self._sync_follow()
        self._update_detail()

    def focused_tree(self) -> SideTree | None:
        if self.focused is self.left or (self.focused and self.focused.id == "left"):
            return self.left
        if self.focused is self.right or (self.focused and self.focused.id == "right"):
            return self.right
        return self.left

    # --- follow mode: mirror cursor position in the other tree ---

    def action_toggle_follow(self) -> None:
        self.follow_mode = not self.follow_mode
        self.query_one("#walk", Static).update(self._walk_label())

    def _sync_follow(self) -> None:
        if not self.follow_mode:
            return
        src = self.focused_tree()
        if src is None:
            return
        cur = src.cursor_node
        if cur is None or cur.data is None:
            return
        align_node = cur.data.align
        if align_node is None:
            return
        other = self.right if src is self.left else self.left
        target_idx = align_node.right_idx if src is self.left else align_node.left_idx
        if target_idx is None:
            return
        # Walk `other` down the same child path. Cheap approach: find a
        # TreeNode whose data.idx matches.
        match = _find_node(other.root, target_idx)
        if match is not None:
            other.select_node(match)

    # --- detail pane ---

    def _update_detail(self) -> None:
        tree = self.focused_tree()
        if tree is None:
            return
        cur = tree.cursor_node
        if cur is None or cur.data is None:
            return
        entry = cur.data
        node = self.dump.nodes.get(entry.idx)
        detail = self.query_one("#detail", Static)
        if node is None:
            detail.update(f"#{entry.idx} <missing>")
            return
        lines = [
            f"{tree.side}  #{entry.idx}  {node.op_display}",
            f"  args:       {list(node.args)}",
            f"  raw_op:     {node.raw_op!r}",
            f"  annotation: {node.annotation or ''}",
        ]
        if entry.align:
            lines.append(f"  align:      {entry.align.status}  (↔ #{entry.align.right_idx if tree.side=='L' else entry.align.left_idx})")
        detail.update("\n".join(lines))

    # --- clustering ---

    def action_cluster(self) -> None:
        tree = self.focused_tree()
        if tree is None:
            return
        cur = tree.cursor_node
        if cur is None or cur.data is None:
            return
        # Rebuild subtree with shared shape hashes collapsed.
        shapes = cluster_shapes(self.dump, cur.data.idx)
        self.notify(
            f"{len(set(shapes.values()))} unique shapes in {len(shapes)} nodes "
            "(cluster collapse coming soon)"
        )

    # --- goto ---

    def action_goto(self) -> None:
        def _on_close(val: int | None) -> None:
            if val is None:
                return
            if val not in self.dump.nodes:
                self.notify(f"idx {val} not in dump", severity="warning")
                return
            # We treat this as a one-off tree rooted at val, with no alignment.
            self.left.mount_root(val, None)
            self.query_one("#walk", Static).update(f"goto #{val}")
        self.push_screen(GotoScreen(), _on_close)

    # --- simulate rewrites ---

    def action_simulate(self) -> None:
        tree = self.focused_tree()
        if tree is None:
            return
        cur = tree.cursor_node
        if cur is None or cur.data is None:
            return
        report = simulate_rewrites(self.dump, cur.data.idx)
        self.query_one("#detail", Static).update(report)


def _find_node(tn: TreeNode[TreeEntry], idx: int) -> TreeNode[TreeEntry] | None:
    """DFS a Textual tree looking for a node whose entry.idx matches.

    Only walks already-expanded branches — the tree is lazy and we don't want
    to trigger population of the whole subgraph just to find a match.
    """
    if tn.data is not None and tn.data.idx == idx:
        return tn
    for c in tn.children:
        found = _find_node(c, idx)
        if found is not None:
            return found
    return None


def run_tui(path: str) -> int:
    dump = parse_file(path)
    app = DagVizApp(dump)
    app.run()
    return 0
