#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**251 - 9' -Dmodulus_bytes='41 + 5/6' -Da24='121665'
