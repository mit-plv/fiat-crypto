#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**321 - 9' -Dmodulus_bytes='20 + 1/16' -Da24='121665'
