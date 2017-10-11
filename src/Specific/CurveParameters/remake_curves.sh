#!/bin/bash

set -ex

cd "$( dirname "${BASH_SOURCE[0]}" )"

MAKE="../Framework/make_curve.py"

${MAKE} "$@" x25519_c64.json ../X25519/C64/
${MAKE} "$@" x25519_c32.json ../X25519/C32/
${MAKE} "$@" x2555_130.json ../X2555/C128/
${MAKE} "$@" x2448_c64_karatsuba.json ../X2448/Karatsuba/C64/
${MAKE} "$@" nistp256_amd128.json ../NISTP256/AMD128/
${MAKE} "$@" nistp256_amd64.json ../NISTP256/AMD64/
