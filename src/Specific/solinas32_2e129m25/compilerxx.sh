#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='21.5' -Dlimb_t=uint32_t -Dq_mpz='(1_mpz<<129) - 25' -Dmodulus_limbs='6' -Dlimb_weight_gaps_array='{22,21,22,21,22,21}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe7}' "$@"
