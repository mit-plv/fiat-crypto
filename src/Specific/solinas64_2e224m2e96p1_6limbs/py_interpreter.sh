#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**224 - 2**96 + 1' -Dmodulus_bytes='37 + 1/3' -Da24='121665'
