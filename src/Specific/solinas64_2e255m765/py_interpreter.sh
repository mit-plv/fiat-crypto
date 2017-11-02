#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**255 - 765' -Dmodulus_bytes='51' -Da24='121665'
