#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**255 - 765' -Dmodulus_bytes='21.25' -Da24='121665'
