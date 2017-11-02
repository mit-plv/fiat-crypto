#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**205 - 45*2**198 - 1' -Dmodulus_bytes='51.25' -Da24='121665'
