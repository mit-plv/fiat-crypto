#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='43 + 1/3' -Dlimb_t=uint64_t -Dq_mpz='(1_mpz<<130) - 5 ' -Dmodulus_limbs='3' -Dlimb_weight_gaps_array='{44,43,43}' -Dmodulus_array='{0x03,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfb}' "$@"
