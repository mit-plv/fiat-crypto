#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='34.25' -Dlimb_t=uint64_t -Dq_mpz='(1_mpz<<137) - 13' -Dmodulus_limbs='4' -Dlimb_weight_gaps_array='{35,34,34,34}' -Dmodulus_array='{0x01,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf3}' "$@"
