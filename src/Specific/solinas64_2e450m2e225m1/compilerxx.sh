#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dq_mpz='(1_mpz<<450) - (1_mpz<<225) - 1' -Dmodulus_bytes_val='56.25' "$@"
