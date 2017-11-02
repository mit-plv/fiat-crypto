#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='3' -Dmodulus_bytes_val='47' -Dlimb_t=uint64_t -Dlimb_weight_gaps_array='{47,47,47}' -Dmodulus_array='{0x1f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf7}' -Dq_mpz='(1_mpz<<141) - 9' "$@"
