#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**213 - 3' -Dmodulus_bytes='42.6' -Da24='121665'
