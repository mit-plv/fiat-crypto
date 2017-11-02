#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<256) - (1_mpz<<32) - 977 ' -Dmodulus_bytes_val='21 + 1/3' "$@"
