#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<255) - (1_mpz<<4) - (1_mpz<<1) - 1' -Dmodulus_bytes_val='51' "$@"
