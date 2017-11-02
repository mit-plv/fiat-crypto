#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**414 - 17' -Dmodulus_bytes='46' -Da24='121665'
