#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**468 - 17' -Dmodulus_bytes='58.5' -Da24='121665'
