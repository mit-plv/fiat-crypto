#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**510 - 290*2**496 - 1' -Dmodulus_bytes='21.25' -Da24='121665'
