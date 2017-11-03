#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**336 - 17' -Dmodulus_bytes='56' -Da24='121665'
