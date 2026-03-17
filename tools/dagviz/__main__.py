"""dagviz CLI entry point.

Usage:

    python -m tools.dagviz trace DUMP --idx N [--depth D] [--no-share]
    python -m tools.dagviz diverge DUMP
    python -m tools.dagviz stats DUMP

These are the text-mode subcommands. The TUI lives in ``tui.py`` and is
invoked via ``python -m tools.dagviz tui DUMP``.
"""

from __future__ import annotations

import argparse
import sys

from .parse import parse_file
from .trace import render_divergence_summary, render_tree


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="dagviz")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_trace = sub.add_parser("trace", help="print an s-expression tree rooted at an idx")
    p_trace.add_argument("dump")
    p_trace.add_argument("--idx", type=int, required=True)
    p_trace.add_argument("--depth", type=int, default=6)
    p_trace.add_argument("--no-share", action="store_true",
                         help="always expand shared subtrees in full")

    p_div = sub.add_parser("diverge", help="print the divergence walk summary")
    p_div.add_argument("dump")

    p_stats = sub.add_parser("stats", help="print high-level dump statistics")
    p_stats.add_argument("dump")

    p_tui = sub.add_parser("tui", help="launch the interactive viewer")
    p_tui.add_argument("dump")

    p_dot = sub.add_parser("dot", help="export a subgraph as graphviz dot")
    p_dot.add_argument("dump")
    p_dot.add_argument("--idx", type=int, required=True)
    p_dot.add_argument("--depth", type=int, default=8)

    args = ap.parse_args(argv)

    if args.cmd == "trace":
        dump = parse_file(args.dump)
        print(render_tree(dump, args.idx, max_depth=args.depth, share=not args.no_share))
        return 0
    if args.cmd == "diverge":
        dump = parse_file(args.dump)
        print(render_divergence_summary(dump))
        return 0
    if args.cmd == "stats":
        dump = parse_file(args.dump)
        print(f"nodes:         {len(dump.nodes)}")
        print(f"reg bindings:  {len(dump.reg_history)}")
        print(f"asm roots:     {len(dump.asm_output_roots)}")
        print(f"phoas roots:   {len(dump.phoas_output_roots)}")
        print(f"divergence:    {len(dump.divergence)} steps")
        op_counts: dict[str, int] = {}
        for n in dump.nodes.values():
            op_counts[n.op_name] = op_counts.get(n.op_name, 0) + 1
        top = sorted(op_counts.items(), key=lambda kv: -kv[1])[:15]
        print("top ops:")
        for name, c in top:
            print(f"  {c:5d}  {name}")
        return 0
    if args.cmd == "dot":
        from .export import to_dot
        dump = parse_file(args.dump)
        print(to_dot(dump, args.idx, max_depth=args.depth))
        return 0
    if args.cmd == "tui":
        try:
            from .tui import run_tui
        except Exception as exc:
            print(f"tui not available: {exc}", file=sys.stderr)
            return 2
        return run_tui(args.dump)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
