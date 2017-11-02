#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**256 - 88*2**240 - 1' -Dmodulus_bytes='64' -Da24='121665'
