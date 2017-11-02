#!/bin/sh
set -eu

g++ -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing -Dq_mpz='(1_mpz<<384) - 79*(1_mpz<<376) - 1' -Dmodulus_bytes_val='64' "$@"
