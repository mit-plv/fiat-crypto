#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**255 - 2**4 - 2**1 - 1' -Dmodulus_bytes='28 + 1/3' -Da24='121665'
