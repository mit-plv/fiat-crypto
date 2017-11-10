#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**165 - 25' -Dmodulus_bytes='20.625' -Da24='121665'
