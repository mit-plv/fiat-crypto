#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='42 + 1/3' -Dlimb_t=uint64_t -Dq_mpz='(1_mpz<<127) - 1 ' -Dmodulus_limbs='3' -Dlimb_weight_gaps_array='{43,42,42}' -Dmodulus_array='{0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff}' "$@"
