#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**256 - 189' -Dmodulus_bytes='23 + 3/11' -Da24='121665'
