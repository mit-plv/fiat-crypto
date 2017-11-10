#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**480 - 2**240 - 1' -Dmodulus_bytes='26 + 2/3' -Da24='121665'
