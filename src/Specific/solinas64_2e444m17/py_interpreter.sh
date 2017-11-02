#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**444 - 17' -Dmodulus_bytes='55.5' -Da24='121665'
