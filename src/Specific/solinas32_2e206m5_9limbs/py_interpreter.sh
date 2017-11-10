#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**206 - 5' -Dmodulus_bytes='22 + 8/9' -Da24='121665'
