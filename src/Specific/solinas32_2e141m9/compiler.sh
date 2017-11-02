#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='23.5' -Dlimb_t=uint32_t -Dq_mpz='(1_mpz<<141) - 9' -Dmodulus_limbs='6' -Dlimb_weight_gaps_array='{24,23,24,23,24,23}' -Dmodulus_array='{0x1f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf7}' "$@"
