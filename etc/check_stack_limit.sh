#!/usr/bin/env bash

set -eu

stacksize="$(ulimit -s || true)"
recstacksize=32768
suggest="Warning: We recommend a stack size of at least $recstacksize kbytes (set with ulimit -S -s $recstacksize) to avoid stack overflows in OCaml compilation."
test ! -z "$stacksize" || { >&2 printf "Warning: Could not determine stack size.\n%s\n" "${suggest}"; exit 1; }
if [ "$stacksize" == "unlimited" ]; then exit 0; fi
# test for integer stacksize
test "$stacksize" -eq "$stacksize" 2>/dev/null || { >&2 printf "Warning: Stack size (%s) could not be parsed as a number.\n%s\n" "$stacksize"  "${suggest}"; exit 1; }
test "$stacksize" -ge "$recstacksize" || { >&2 printf "Warning: Stack size (%s) may be too small.\n%s\n" "$stacksize" "${suggest}"; exit 1; }
