#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**152 - 17' -Dmodulus_bytes='25 + 1/3' -Da24='121665'
