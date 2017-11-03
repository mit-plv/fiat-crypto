#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**222 - 117' -Dmodulus_bytes='64' -Da24='121665'
