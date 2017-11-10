#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**511 - 187' -Dmodulus_bytes='22 + 5/23' -Da24='121665'
