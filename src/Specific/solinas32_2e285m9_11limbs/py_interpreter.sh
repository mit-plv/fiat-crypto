#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**285 - 9' -Dmodulus_bytes='25 + 10/11' -Da24='121665'
