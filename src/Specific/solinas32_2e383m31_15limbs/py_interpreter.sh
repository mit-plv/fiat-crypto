#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**383 - 31' -Dmodulus_bytes='25 + 8/15' -Da24='121665'
