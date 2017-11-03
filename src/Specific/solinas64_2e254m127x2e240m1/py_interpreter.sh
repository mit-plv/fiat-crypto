#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**254 - 127*2**240 - 1' -Dmodulus_bytes='42 + 1/3' -Da24='121665'
