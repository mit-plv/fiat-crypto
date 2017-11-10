#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**512 - 491*2**496 - 1' -Dmodulus_bytes='32' -Da24='121665'
