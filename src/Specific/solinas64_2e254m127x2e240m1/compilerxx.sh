#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<254) - 127*(1_mpz<<240) - 1' -Dmodulus_bytes_val='42 + 1/3' "$@"
