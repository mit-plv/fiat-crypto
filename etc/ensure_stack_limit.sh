#!/usr/bin/env bash

set -eu

recstacksize=32768
if command -v ulimit >/dev/null 2>/dev/null; then
    hardstacksize="$(ulimit -H -s || true)"
    (
        stacksize="$(ulimit -S -s || true)"
        test ! -z "$stacksize" || { >&2 printf "Warning: Could not determine stack size.\n"; exit 1; }
        # unlimited stack is fine.  N.B. == is not fully POSIX-compliant, so we need != or ==
        test "$stacksize" != "unlimited" || exit 0
        # test for integer stacksize
        test "$stacksize" -eq "$stacksize" 2>/dev/null || { >&2 printf "Warning: Stack size (%s) could not be parsed as a number.\n" "$stacksize"; exit 1; }
        test "$stacksize" -ge "$recstacksize" || { >&2 printf "Warning: Stack size (%s) may be too small.\n" "$stacksize"; exit 1; }
    ) || {
        >&2 printf "Warning: To avoid stack overflows in OCaml compilation, setting stack size to the recommended minimum of %s kbytes\n" "$recstacksize"
        ulimit -S -s "$recstacksize" || { >&2 printf "Warning: Failed to set stack size to %s, possibly because the hard stack size limit is %s.\n" "$recstacksize" "$hardstacksize"; exit 1; }
    }
else
    >&2 printf "Warning: Could not determine stack size because ulimit was not found.\nWarning: We recommend a stack size of at least %s kbytes to avoid stack overflows in OCaml compilation.\n" "$recstacksize"
fi
