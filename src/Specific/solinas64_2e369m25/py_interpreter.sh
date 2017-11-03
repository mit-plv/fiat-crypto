#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**369 - 25' -Dmodulus_bytes='46.125' -Da24='121665'
