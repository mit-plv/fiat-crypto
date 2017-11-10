#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**266 - 3' -Dmodulus_bytes='44 + 1/3' -Da24='121665'
