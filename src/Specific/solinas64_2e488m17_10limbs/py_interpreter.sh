#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**488 - 17' -Dmodulus_bytes='48.8' -Da24='121665'
