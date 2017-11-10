#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**468 - 17' -Dmodulus_bytes='24 + 12/19' -Da24='121665'
