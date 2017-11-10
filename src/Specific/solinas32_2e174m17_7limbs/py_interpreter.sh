#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**174 - 17' -Dmodulus_bytes='24 + 6/7' -Da24='121665'
