#!/bin/sh
set -eu

g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_limbs='4' -Dmodulus_bytes_val='34.25' -Dlimb_t=uint64_t -Dlimb_weight_gaps_array='{35,34,34,34}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf3}' -Dq_mpz='(1_mpz<<137) - 13' "$@"
