#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**140 - 27' -Dmodulus_bytes='46 + 2/3' -Da24='121665'
