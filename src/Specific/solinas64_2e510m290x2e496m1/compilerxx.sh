#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<510) - 290*(1_mpz<<496) - 1' -Dmodulus_bytes_val='51' "$@"
