#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**384 - 79*2**376 - 1' -Dmodulus_bytes='48' -Da24='121665'
