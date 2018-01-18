#!/bin/sh
set -eu

gcc -march=native -mbmi2 -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes "$@"
