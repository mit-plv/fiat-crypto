#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**448-2**224-1' -Dmodulus_bytes='56' -Da24='121665'
