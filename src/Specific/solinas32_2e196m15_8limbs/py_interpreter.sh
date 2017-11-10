#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**196 - 15' -Dmodulus_bytes='24.5' -Da24='121665'
