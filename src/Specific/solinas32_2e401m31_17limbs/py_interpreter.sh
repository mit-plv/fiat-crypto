#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**401 - 31' -Dmodulus_bytes='23 + 10/17' -Da24='121665'
