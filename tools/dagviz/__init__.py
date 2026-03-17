"""DAG visualization/debugging tool for fiat-crypto equivalence checker dumps.

Usage:

    python -m tools.dagviz stats   DUMP
    python -m tools.dagviz diverge DUMP
    python -m tools.dagviz trace   DUMP --idx N [--depth D]
    python -m tools.dagviz dot     DUMP --idx N [--depth D]   # → stdout
    python -m tools.dagviz tui     DUMP                        # interactive

Primary goal: make it fast to see *why* two DAG subtrees fail to unify in
the equivalence checker. The TUI walks the divergence trace step by step,
with structural alignment recolouring matching vs mismatching branches.

Depends on ``textual`` + ``rich`` (see requirements.txt).
"""
