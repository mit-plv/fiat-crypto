#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**489 - 21' -Dmodulus_bytes='48.9' -Da24='121665'
