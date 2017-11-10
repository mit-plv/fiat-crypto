#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**256 - 2**32 - 977' -Dmodulus_bytes='36 + 4/7' -Da24='121665'
