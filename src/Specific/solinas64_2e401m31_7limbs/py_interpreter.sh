#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**401 - 31' -Dmodulus_bytes='57 + 2/7' -Da24='121665'
