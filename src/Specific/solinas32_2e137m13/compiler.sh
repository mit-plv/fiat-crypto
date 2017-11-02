#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='8' -Dmodulus_bytes_val='17.125' -Dlimb_t=uint32_t -Dlimb_weight_gaps_array='{18,17,17,17,17,17,17,17}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf3}' -Dq_mpz='(1_mpz<<137) - 13' "$@"
