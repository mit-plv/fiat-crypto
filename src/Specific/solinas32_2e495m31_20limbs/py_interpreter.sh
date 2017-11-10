#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**495 - 31' -Dmodulus_bytes='24.75' -Da24='121665'
