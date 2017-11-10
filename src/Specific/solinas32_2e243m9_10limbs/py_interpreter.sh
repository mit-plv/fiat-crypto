#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**243 - 9' -Dmodulus_bytes='24.3' -Da24='121665'
