#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**512 - 569' -Dmodulus_bytes='46 + 6/11' -Da24='121665'
