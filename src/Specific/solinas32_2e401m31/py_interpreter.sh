#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**401 - 31' -Dmodulus_bytes='25 + 1/16' -Da24='121665'
