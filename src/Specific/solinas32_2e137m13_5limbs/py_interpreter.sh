#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**137 - 13' -Dmodulus_bytes='27.4' -Da24='121665'
