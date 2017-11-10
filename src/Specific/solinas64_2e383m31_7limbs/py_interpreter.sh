#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**383 - 31' -Dmodulus_bytes='54 + 5/7' -Da24='121665'
