#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**495 - 31' -Dmodulus_bytes='26 + 1/19' -Da24='121665'
