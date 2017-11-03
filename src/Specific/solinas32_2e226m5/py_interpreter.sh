#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**226 - 5' -Dmodulus_bytes='28.25' -Da24='121665'
