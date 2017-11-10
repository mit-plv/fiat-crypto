#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**127 - 1' -Dmodulus_bytes='25.4' -Da24='121665'
