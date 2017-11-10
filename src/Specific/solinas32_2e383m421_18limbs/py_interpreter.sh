#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**383 - 421' -Dmodulus_bytes='21 + 5/18' -Da24='121665'
