#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**291 - 19' -Dmodulus_bytes='58.2' -Da24='121665'
