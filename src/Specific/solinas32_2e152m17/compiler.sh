#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='25 + 1/3' -Dlimb_t=uint32_t -Dq_mpz='(1_mpz<<152) - 17' -Dmodulus_limbs='6' -Dlimb_weight_gaps_array='{26,25,25,26,25,25}' -Dmodulus_array='{0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xef}' "$@"
