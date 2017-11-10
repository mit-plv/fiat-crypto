#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**291 - 19' -Dmodulus_bytes='26 + 5/11' -Da24='121665'
