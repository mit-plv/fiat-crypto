#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**384 - 5*2**368 - 1' -Dmodulus_bytes='48' -Da24='121665'
