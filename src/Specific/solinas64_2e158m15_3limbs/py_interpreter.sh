#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**158 - 15' -Dmodulus_bytes='52 + 2/3' -Da24='121665'
