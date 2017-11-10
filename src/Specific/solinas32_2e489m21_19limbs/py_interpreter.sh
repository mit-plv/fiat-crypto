#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**489 - 21' -Dmodulus_bytes='25 + 14/19' -Da24='121665'
