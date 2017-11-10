#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**413 - 21' -Dmodulus_bytes='25 + 13/16' -Da24='121665'
