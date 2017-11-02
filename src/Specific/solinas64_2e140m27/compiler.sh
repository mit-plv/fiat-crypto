#!/bin/sh
set -eu

gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Dmodulus_bytes_val='35' -Dlimb_t=uint64_t -Dq_mpz='(1_mpz<<140) - 27' -Dmodulus_limbs='4' -Dlimb_weight_gaps_array='{35,35,35,35}' -Dmodulus_array='{0x0f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe5}' "$@"
