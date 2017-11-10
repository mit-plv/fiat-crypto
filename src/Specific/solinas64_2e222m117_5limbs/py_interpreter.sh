#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**222 - 117' -Dmodulus_bytes='44.4' -Da24='121665'
