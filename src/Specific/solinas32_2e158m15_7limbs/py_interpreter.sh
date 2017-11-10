#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**158 - 15' -Dmodulus_bytes='22 + 4/7' -Da24='121665'
