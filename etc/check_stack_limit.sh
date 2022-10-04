#!/usr/bin/env bash

set -eu

stacksize="$(ulimit -s || true)"
recstacksize=32768
nl=$'\n'
suggest="Warning: We recommend a stack size of at least $recstacksize kbytes (set with ulimit -S -s $recstacksize) to avoid stack overflows in OCaml compilation."
test ! -z "$stacksize" || { >&2 echo "Warning: Could not determine stack size.${nl}${suggest}"; exit 1; }
if [ "$stacksize" == "unlimited" ]; then exit 0; fi
# test for integer stacksize
test "$stacksize" -eq "$stacksize" 2>/dev/null || { >&2 echo "Warning: Stack size ($stacksize) could not be parsed as a number.${nl}${suggest}"; exit 1; }
test "$stacksize" -ge "$recstacksize" || { >&2 echo "Warning: Stack size ($stacksize) may be too small.${nl}${suggest}"; exit 1; }
