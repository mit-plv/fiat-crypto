#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**256 - 4294968273' -Dmodulus_bytes='64' -Da24='121665'
