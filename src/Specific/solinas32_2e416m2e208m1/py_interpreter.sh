#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**416 - 2**208 - 1' -Dmodulus_bytes='26' -Da24='121665'
