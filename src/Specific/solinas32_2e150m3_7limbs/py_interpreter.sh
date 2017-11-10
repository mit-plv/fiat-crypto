#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**150 - 3' -Dmodulus_bytes='21 + 3/7' -Da24='121665'
