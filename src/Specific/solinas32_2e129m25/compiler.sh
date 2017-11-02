#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='6' -Dmodulus_bytes_val='21.5' -Dlimb_t=uint32_t -Dlimb_weight_gaps_array='{22,21,22,21,22,21}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe7}' -Dq_mpz='(1_mpz<<129) - 25' "$@"
