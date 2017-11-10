#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**256 - 189' -Dmodulus_bytes='42 + 2/3' -Da24='121665'
