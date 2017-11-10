#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**266 - 3' -Dmodulus_bytes='24 + 2/11' -Da24='121665'
