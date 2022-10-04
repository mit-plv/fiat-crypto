#!/usr/bin/env bash

stacksize="$(ulimit -s)"
recstacksize=32768
if [ ! -z "$stacksize" ]; then
    if test "$stacksize" -eq "$stacksize" 2>/dev/null; then
        if [ "$stacksize" -ge "$recstacksize" ]; then
            exit 0
        else
            >&2 echo "Warning: Stack size ($stacksize) may be too small."
        fi
    elif [ "$stacksize" == "unlimited" ]; then
        exit 0
    else
        >&2 echo "Warning: Stack size ($stacksize) could not be parsed as a number."
    fi
else
    >&2 echo "Warning: Could not determine stack size."
fi
>&2 echo "Warning: We recommend a stack size of at least $recstacksize kbytes (set with ulimit -S -s $recstacksize) to avoid stack overflows in OCaml compilation."
exit 1
