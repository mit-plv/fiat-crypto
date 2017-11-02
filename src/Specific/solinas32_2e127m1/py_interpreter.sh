#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**127 - 1 ' -Dmodulus_bytes='21 + 1/6' -Da24='121665'
