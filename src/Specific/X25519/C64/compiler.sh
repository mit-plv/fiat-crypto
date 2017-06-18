#!/bin/sh
set -euo pipefail

gcc -march=native -mtune=native -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes $@
