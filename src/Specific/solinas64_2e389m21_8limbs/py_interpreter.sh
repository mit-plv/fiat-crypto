#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**389 - 21' -Dmodulus_bytes='48.625' -Da24='121665'
