#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**512 - 569' -Dmodulus_bytes='20 + 12/25' -Da24='121665'
