#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**212 - 29' -Dmodulus_bytes='53' -Da24='121665'
