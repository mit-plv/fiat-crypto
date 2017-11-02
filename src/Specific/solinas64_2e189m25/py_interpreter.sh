#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**189 - 25' -Dmodulus_bytes='47.25' -Da24='121665'
