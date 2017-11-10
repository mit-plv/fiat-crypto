#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**521 - 1' -Dmodulus_bytes='26 + 1/20' -Da24='121665'
