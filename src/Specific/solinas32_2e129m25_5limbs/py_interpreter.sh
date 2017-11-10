#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**129 - 25' -Dmodulus_bytes='25.8' -Da24='121665'
