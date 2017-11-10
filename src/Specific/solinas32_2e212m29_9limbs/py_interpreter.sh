#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**212 - 29' -Dmodulus_bytes='23 + 5/9' -Da24='121665'
