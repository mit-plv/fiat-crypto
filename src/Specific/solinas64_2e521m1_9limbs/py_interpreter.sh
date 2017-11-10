#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**521 - 1' -Dmodulus_bytes='57 + 8/9' -Da24='121665'
