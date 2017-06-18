#!/bin/sh
set -e || true
set -u || true
set -o pipefail || true

gcc -march=native -mtune=native -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes $@
