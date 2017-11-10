#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**226 - 5' -Dmodulus_bytes='45.2' -Da24='121665'
