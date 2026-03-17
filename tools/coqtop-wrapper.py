#!/usr/bin/env python3
"""
coqtop-wrapper.py — Interactive Rocq/Coq proof assistant wrapper for CLI agents.

Manages a persistent coqtop session over stdin/stdout pipes.
Supports: loading files, running tactics, inspecting goals, checking terms.

Usage:
  # Start a session (loads project paths from _CoqProject)
  python3 tools/coqtop-wrapper.py start [--project /path/to/_CoqProject]

  # Run a command in the session
  python3 tools/coqtop-wrapper.py run "intros n m."

  # Get current goals
  python3 tools/coqtop-wrapper.py goals

  # Load a file up to a specific line (replays source up to that point)
  python3 tools/coqtop-wrapper.py load-to src/Assembly/Symbolic.v 330

  # Check a term
  python3 tools/coqtop-wrapper.py run "Check op_beq_spec."

  # Stop the session
  python3 tools/coqtop-wrapper.py stop
"""

import subprocess
import os
import sys
import json
import select
import time
import re
import argparse
import fcntl

STATEFILE = "/tmp/coqtop-session.json"
FIFOIN = "/tmp/coqtop-in.fifo"
PIDFILE = "/tmp/coqtop-wrapper.pid"

# ---------- coqtop process management ----------

def parse_coqproject(path):
    """Extract -R, -Q, -I flags from a _CoqProject file."""
    flags = []
    if not os.path.exists(path):
        return flags
    with open(path) as f:
        tokens = []
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            tokens.extend(line.split())

    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ('-R', '-Q') and i + 2 < len(tokens):
            flags.extend([tok, tokens[i+1], tokens[i+2]])
            i += 3
        elif tok == '-I' and i + 1 < len(tokens):
            flags.extend([tok, tokens[i+1]])
            i += 2
        elif tok == '-arg' and i + 1 < len(tokens):
            # Skip -arg flags (warnings etc) — not needed for coqtop
            i += 2
        else:
            i += 1
    return flags


def build_coqtop_cmd(project_path=None):
    """Build the coqtop command with appropriate load paths."""
    cmd = ["coqtop", "-q", "-emacs"]  # -q=quiet, -emacs=structured output

    if project_path is None:
        # Auto-detect: walk up from cwd looking for _CoqProject
        d = os.getcwd()
        while d != '/':
            cp = os.path.join(d, '_CoqProject')
            if os.path.exists(cp):
                project_path = cp
                break
            d = os.path.dirname(d)

    if project_path:
        project_dir = os.path.dirname(os.path.abspath(project_path))
        flags = parse_coqproject(project_path)
        # Make relative paths absolute based on project dir
        resolved = []
        i = 0
        while i < len(flags):
            if flags[i] in ('-R', '-Q') and i + 2 < len(flags):
                path = flags[i+1]
                if not os.path.isabs(path):
                    path = os.path.join(project_dir, path)
                resolved.extend([flags[i], path, flags[i+2]])
                i += 3
            elif flags[i] == '-I' and i + 1 < len(flags):
                path = flags[i+1]
                if not os.path.isabs(path):
                    path = os.path.join(project_dir, path)
                resolved.extend(['-I', path])
                i += 2
            else:
                resolved.append(flags[i])
                i += 1
        cmd.extend(resolved)
    return cmd


class CoqSession:
    """Manages a coqtop subprocess with structured I/O."""

    # coqtop -emacs wraps output in XML-like tags
    PROMPT_RE = re.compile(r'<prompt>.*?</prompt>', re.DOTALL)
    TAG_RE = re.compile(r'</?(?:prompt|warning|infomsg|errormsg)>')
    ID_RE = re.compile(r'\s*\(ID \d+\)')

    def __init__(self, cmd):
        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
        )
        # Set stdout non-blocking for reads
        fd = self.proc.stdout.fileno()
        fl = fcntl.fcntl(fd, fcntl.F_GETFL)
        fcntl.fcntl(fd, fcntl.F_SETFL, fl | os.O_NONBLOCK)

        # Drain initial banner/prompt
        self._drain(timeout=3)

    def _drain(self, timeout=10):
        """Read all available output, waiting for a prompt."""
        buf = b""
        deadline = time.time() + timeout
        last_data = time.time()
        while time.time() < deadline:
            ready, _, _ = select.select([self.proc.stdout.fileno()], [], [], 0.3)
            if ready:
                try:
                    chunk = os.read(self.proc.stdout.fileno(), 65536)
                    if chunk:
                        buf += chunk
                        last_data = time.time()
                        # Check if we got a prompt (coqtop -emacs sends <prompt>)
                        if b'</prompt>' in buf:
                            break
                    else:
                        break
                except BlockingIOError:
                    pass
            elif buf and (time.time() - last_data) > 1.5:
                break
        return buf.decode(errors='replace')

    def send(self, command, timeout=60):
        """Send a command to coqtop and return the response."""
        if self.proc.poll() is not None:
            return {"error": "coqtop process has exited"}

        data = command.strip() + "\n"
        try:
            os.write(self.proc.stdin.fileno(), data.encode())
        except BrokenPipeError:
            return {"error": "coqtop process has exited"}

        raw = self._drain(timeout=timeout)

        # Strip XML tags from -emacs mode, clean up goal IDs
        clean = self.PROMPT_RE.sub('', raw)
        clean = self.TAG_RE.sub('', clean)
        clean = self.ID_RE.sub('', clean)
        clean = clean.strip()
        return {"output": clean}

    def alive(self):
        return self.proc.poll() is None

    def kill(self):
        if self.alive():
            self.proc.terminate()
            try:
                self.proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                self.proc.kill()


# ---------- Session persistence via a background process ----------

def start_session(project_path=None):
    """Start a new coqtop session, saving state for later commands."""
    # Kill any existing session
    stop_session()

    cmd = build_coqtop_cmd(project_path)
    session = CoqSession(cmd)

    if not session.alive():
        print(json.dumps({"error": "coqtop failed to start"}))
        sys.exit(1)

    # Save session info
    state = {
        "pid": session.proc.pid,
        "cmd": cmd,
        "started": time.time(),
    }
    with open(STATEFILE, 'w') as f:
        json.dump(state, f)

    # Return the session for immediate use
    return session


def get_session():
    """Reconnect to existing session or start a new one."""
    if not os.path.exists(STATEFILE):
        return None
    with open(STATEFILE) as f:
        state = json.load(f)

    pid = state.get("pid")
    if pid:
        try:
            os.kill(pid, 0)  # Check if process exists
        except ProcessLookupError:
            os.unlink(STATEFILE)
            return None

    # Can't reconnect to a running coqtop — it owns its pipes.
    # We need to keep the CoqSession object alive.
    return None


def stop_session():
    """Stop any running session."""
    if os.path.exists(STATEFILE):
        with open(STATEFILE) as f:
            state = json.load(f)
        pid = state.get("pid")
        if pid:
            try:
                os.kill(pid, 9)
            except ProcessLookupError:
                pass
        os.unlink(STATEFILE)


# ---------- Stateless mode (run everything in one shot) ----------

def run_oneshot(commands, project_path=None, timeout=120):
    """Run a sequence of commands in a fresh coqtop, return all output."""
    cmd = build_coqtop_cmd(project_path)
    session = CoqSession(cmd)
    results = []
    for c in commands:
        if not session.alive():
            results.append({"command": c, "error": "coqtop exited"})
            break
        r = session.send(c, timeout=timeout)
        r["command"] = c
        results.append(r)
    session.kill()
    return results


def load_file_to(filepath, line_number, project_path=None):
    """Load a .v file up to a given line number, return the state at that point.

    This replays the file's source up to the specified line through coqtop,
    then returns the goals/context at that point.
    """
    if not os.path.exists(filepath):
        return {"error": f"File not found: {filepath}"}

    with open(filepath) as f:
        lines = f.readlines()

    # Take lines up to the target
    source = "".join(lines[:line_number])

    # Split into sentences (rough: split on '.' followed by whitespace/EOF)
    # This is a simplification — a proper parser would handle strings/comments
    sentences = split_into_sentences(source)

    cmd = build_coqtop_cmd(project_path)
    session = CoqSession(cmd)

    last_output = ""
    for i, sent in enumerate(sentences):
        sent = sent.strip()
        if not sent:
            continue
        r = session.send(sent, timeout=120)
        if "error" in r:
            session.kill()
            return {"error": r["error"], "at_sentence": i, "sentence": sent}
        last_output = r.get("output", "")
        if "Error:" in last_output:
            session.kill()
            return {"error": last_output, "at_sentence": i, "sentence": sent}

    # Now get goals
    r = session.send("Show.", timeout=10)
    goals_output = r.get("output", "")
    session.kill()

    return {
        "state": goals_output if goals_output else "(no goals)",
        "sentences_loaded": len(sentences),
        "up_to_line": line_number,
    }


def split_into_sentences(source):
    """Split Coq source into sentences (period-terminated commands).

    Handles: string literals, comments, bullets/braces.
    This is approximate but works for most practical code.
    """
    sentences = []
    current = []
    i = 0
    in_string = False
    comment_depth = 0

    while i < len(source):
        c = source[i]

        # Handle strings
        if c == '"' and comment_depth == 0:
            in_string = not in_string
            current.append(c)
            i += 1
            continue

        if in_string:
            current.append(c)
            i += 1
            continue

        # Handle comments
        if c == '(' and i + 1 < len(source) and source[i+1] == '*':
            comment_depth += 1
            current.append(c)
            i += 1
            current.append(source[i])
            i += 1
            continue

        if c == '*' and i + 1 < len(source) and source[i+1] == ')' and comment_depth > 0:
            comment_depth -= 1
            current.append(c)
            i += 1
            current.append(source[i])
            i += 1
            continue

        if comment_depth > 0:
            current.append(c)
            i += 1
            continue

        # Sentence terminators
        if c == '.':
            # Check if this is a sentence-ending dot:
            # Must be followed by whitespace, EOF, or ')' or another dot won't work
            next_i = i + 1
            if next_i >= len(source) or source[next_i] in (' ', '\t', '\n', '\r'):
                current.append(c)
                sentences.append("".join(current).strip())
                current = []
                i = next_i
                continue
            # Could be a qualified name like Nat.add — not a sentence terminator
            # But ".." or "..." are bullets
            if next_i < len(source) and source[next_i] == '.':
                # Bullet: .. or ...
                dots = '.'
                while next_i < len(source) and source[next_i] == '.':
                    dots += '.'
                    next_i += 1
                current.append(dots)
                sentences.append("".join(current).strip())
                current = []
                i = next_i
                continue

        # Braces and bullets as sentence separators
        if c in ('{', '}') and comment_depth == 0:
            if current and "".join(current).strip():
                sentences.append("".join(current).strip())
                current = []
            sentences.append(c)
            i += 1
            continue

        if c in ('-', '+', '*') and comment_depth == 0:
            # Check if it's a bullet (same char repeated, at start of line or after whitespace)
            bullet = c
            j = i + 1
            while j < len(source) and source[j] == c:
                bullet += c
                j += 1
            # Bullets are followed by whitespace
            if j < len(source) and source[j] in (' ', '\t', '\n'):
                # Check if we're at start of logical line
                pre = "".join(current).strip()
                if not pre:
                    sentences.append(bullet)
                    current = []
                    i = j
                    continue

        current.append(c)
        i += 1

    # Remaining text
    remainder = "".join(current).strip()
    if remainder:
        sentences.append(remainder)

    return sentences


# ---------- CLI interface ----------

def main():
    parser = argparse.ArgumentParser(
        description="Interactive Rocq/Coq proof assistant wrapper",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument('--project', '-p', default=None,
                        help='Path to _CoqProject file (auto-detected if omitted)')
    parser.add_argument('--timeout', '-t', type=int, default=60,
                        help='Timeout per command in seconds')
    parser.add_argument('--json', action='store_true',
                        help='Output results as JSON')

    sub = parser.add_subparsers(dest='action')

    # run: execute one or more commands
    p_run = sub.add_parser('run', help='Run Coq command(s)')
    p_run.add_argument('commands', nargs='+', help='Coq commands to execute')

    # goals: show current goals (alias for "run Show.")
    sub.add_parser('goals', help='Show current proof goals')

    # load-to: load file up to a line
    p_load = sub.add_parser('load-to', help='Load a .v file up to a line number')
    p_load.add_argument('file', help='Path to .v file')
    p_load.add_argument('line', type=int, help='Line number to load up to')

    # check: type-check a term
    p_check = sub.add_parser('check', help='Check/print type of a term')
    p_check.add_argument('term', help='Term to check')

    # search: search for lemmas
    p_search = sub.add_parser('search', help='Search for lemmas matching a pattern')
    p_search.add_argument('pattern', help='Search pattern')

    args = parser.parse_args()

    if args.action is None:
        parser.print_help()
        sys.exit(1)

    def output(result):
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            if isinstance(result, dict):
                if "error" in result:
                    print(f"Error: {result['error']}", file=sys.stderr)
                    sys.exit(1)
                elif "output" in result:
                    print(result["output"])
                elif "state" in result:
                    print(result["state"])
                else:
                    print(json.dumps(result, indent=2))
            elif isinstance(result, list):
                for r in result:
                    if "output" in r:
                        print(r["output"])
                    elif "error" in r:
                        print(f"Error: {r['error']}", file=sys.stderr)

    if args.action == 'run':
        results = run_oneshot(args.commands, project_path=args.project,
                             timeout=args.timeout)
        output(results)

    elif args.action == 'goals':
        results = run_oneshot(["Show."], project_path=args.project,
                             timeout=args.timeout)
        output(results)

    elif args.action == 'load-to':
        result = load_file_to(args.file, args.line, project_path=args.project)
        output(result)

    elif args.action == 'check':
        term = args.term.rstrip('.')
        results = run_oneshot([f"Check {term}."], project_path=args.project,
                             timeout=args.timeout)
        output(results)

    elif args.action == 'search':
        results = run_oneshot([f"Search {args.pattern}."],
                             project_path=args.project, timeout=args.timeout)
        output(results)


if __name__ == '__main__':
    main()
