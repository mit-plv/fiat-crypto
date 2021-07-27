#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
cd ..

fiat-amd64/gentest.py fiat-amd64/*.asm | while IFS= read -r line; do eval $line 2>/dev/null > /dev/null && echo "$line" || echo "# $line" ; done
