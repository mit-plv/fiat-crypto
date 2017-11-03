#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq='2**255-5' -Dmodulus_bytes='130' -Da24='121665 (* XXX TODO(andreser) FIXME?  Is this right for this curve? *)'
