#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**235 - 15' -Dmodulus_bytes='23.5' -Da24='121665'
