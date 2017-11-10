#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**383 - 421' -Dmodulus_bytes='22 + 9/17' -Da24='121665'
