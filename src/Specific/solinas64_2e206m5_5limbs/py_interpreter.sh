#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**206 - 5' -Dmodulus_bytes='41.2' -Da24='121665'
