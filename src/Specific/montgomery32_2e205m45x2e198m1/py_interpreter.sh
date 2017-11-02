#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**205 - 45*2**198 - 1' -Dmodulus_bytes='32' -Da24='121665'
