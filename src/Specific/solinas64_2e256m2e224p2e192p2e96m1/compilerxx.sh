#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<256) - (1_mpz<<224) + (1_mpz<<192) + (1_mpz<<96) - 1 ' -Dmodulus_bytes_val='51.2' "$@"
