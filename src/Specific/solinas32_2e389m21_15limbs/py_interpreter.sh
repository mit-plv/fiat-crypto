#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**389 - 21' -Dmodulus_bytes='25 + 14/15' -Da24='121665'
