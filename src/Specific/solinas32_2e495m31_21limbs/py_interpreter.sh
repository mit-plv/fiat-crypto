#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**495 - 31' -Dmodulus_bytes='23 + 4/7' -Da24='121665'
