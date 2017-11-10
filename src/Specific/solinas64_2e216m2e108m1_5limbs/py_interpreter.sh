#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**216 - 2**108 - 1' -Dmodulus_bytes='43.2' -Da24='121665'
