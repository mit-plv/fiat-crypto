#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='3' -Dmodulus_bytes_val='43' -Dlimb_t=uint64_t -Dlimb_weight_gaps_array='{43,43,43}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe7}' -Dq_mpz='(1_mpz<<129) - 25' "$@"
