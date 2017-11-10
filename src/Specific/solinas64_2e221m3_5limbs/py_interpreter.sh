#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**221 - 3' -Dmodulus_bytes='44.2' -Da24='121665'
