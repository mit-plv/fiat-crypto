#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**511 - 187' -Dmodulus_bytes='18.25' -Da24='121665'
