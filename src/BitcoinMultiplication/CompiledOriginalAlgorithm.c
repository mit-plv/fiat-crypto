#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <stdlib.h>

typedef unsigned char fiat_uint1;
typedef signed char fiat_int1;
#if defined(__GNUC__) || defined(__clang__)
#  define FIAT_FIAT_EXTENSION __extension__
#  define FIAT_FIAT_INLINE __inline__
#else
#  define FIAT_FIAT_EXTENSION
#  define FIAT_FIAT_INLINE
#endif

FIAT_FIAT_EXTENSION typedef signed __int128 fiat_int128;
FIAT_FIAT_EXTENSION typedef unsigned __int128 fiat_uint128;

/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 *   arg2: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 */
static FIAT_FIAT_INLINE void bitcoin_mul_u64(uint64_t out1[5], const uint64_t arg1[5], const uint64_t arg2[5]) {
  fiat_uint128 x1;
  fiat_uint128 x2;
  fiat_uint128 x3;
  uint64_t x4;
  fiat_uint128 x5;
  fiat_uint128 x6;
  fiat_uint128 x7;
  fiat_uint128 x8;
  fiat_uint128 x9;
  fiat_uint128 x10;
  fiat_uint128 x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  uint64_t x15;
  uint64_t x16;
  x1 = ((fiat_uint128)(arg1[4]) * (arg2[4]));
  x2 = (((fiat_uint128)(uint64_t)(x1 & UINT64_C(0xfffffffffffff)) * UINT64_C(0x1000003d10)) + (((((fiat_uint128)(arg1[3]) * (arg2[0])) + ((fiat_uint128)(arg1[2]) * (arg2[1]))) + ((fiat_uint128)(arg1[1]) * (arg2[2]))) + ((fiat_uint128)(arg1[0]) * (arg2[3]))));
  x3 = (((fiat_uint128)(uint64_t)(x1 >> 52) * UINT64_C(0x1000003d10)) + ((uint64_t)(x2 >> 52) + ((((((fiat_uint128)(arg1[4]) * (arg2[0])) + ((fiat_uint128)(arg1[3]) * (arg2[1]))) + ((fiat_uint128)(arg1[2]) * (arg2[2]))) + ((fiat_uint128)(arg1[1]) * (arg2[3]))) + ((fiat_uint128)(arg1[0]) * (arg2[4])))));
  x4 = (uint64_t)(x3 & UINT64_C(0xfffffffffffff));
  x5 = ((uint64_t)(x3 >> 52) + (((((fiat_uint128)(arg1[4]) * (arg2[1])) + ((fiat_uint128)(arg1[3]) * (arg2[2]))) + ((fiat_uint128)(arg1[2]) * (arg2[3]))) + ((fiat_uint128)(arg1[1]) * (arg2[4]))));
  x6 = (((fiat_uint128)((x4 >> 48) + ((uint64_t)(x5 & UINT64_C(0xfffffffffffff)) << 4)) * UINT64_C(0x1000003d1)) + ((fiat_uint128)(arg1[0]) * (arg2[0])));
  x7 = ((uint64_t)(x5 >> 52) + ((((fiat_uint128)(arg1[4]) * (arg2[2])) + ((fiat_uint128)(arg1[3]) * (arg2[3]))) + ((fiat_uint128)(arg1[2]) * (arg2[4]))));
  x8 = (((fiat_uint128)(uint64_t)(x7 & UINT64_C(0xfffffffffffff)) * UINT64_C(0x1000003d10)) + ((uint64_t)(x6 >> 52) + (((fiat_uint128)(arg1[1]) * (arg2[0])) + ((fiat_uint128)(arg1[0]) * (arg2[1])))));
  x9 = ((uint64_t)(x7 >> 52) + (((fiat_uint128)(arg1[4]) * (arg2[3])) + ((fiat_uint128)(arg1[3]) * (arg2[4]))));
  x10 = (((fiat_uint128)(uint64_t)(x9 & UINT64_C(0xfffffffffffff)) * UINT64_C(0x1000003d10)) + ((uint64_t)(x8 >> 52) + ((((fiat_uint128)(arg1[2]) * (arg2[0])) + ((fiat_uint128)(arg1[1]) * (arg2[1]))) + ((fiat_uint128)(arg1[0]) * (arg2[2])))));
  x11 = (((fiat_uint128)(uint64_t)(x9 >> 52) * UINT64_C(0x1000003d10)) + ((uint64_t)(x10 >> 52) + (uint64_t)(x2 & UINT64_C(0xfffffffffffff))));
  x12 = (uint64_t)(x6 & UINT64_C(0xfffffffffffff));
  x13 = (uint64_t)(x8 & UINT64_C(0xfffffffffffff));
  x14 = (uint64_t)(x10 & UINT64_C(0xfffffffffffff));
  x15 = (uint64_t)(x11 & UINT64_C(0xfffffffffffff));
  x16 = ((uint64_t)(x11 >> 52) + (x4 & UINT64_C(0xffffffffffff)));
  out1[0] = x12;
  out1[1] = x13;
  out1[2] = x14;
  out1[3] = x15;
  out1[4] = x16;
}

int main() {
    srand(time(NULL));

    uint64_t arg1[5] = {rand(), rand(), rand(), rand(), rand()};
    uint64_t arg2[5] = {rand(), rand(), rand(), rand(), rand()};
    uint64_t out[5];

    bitcoin_mul_u64(out, arg1, arg2);

    printf("arg1: [");
    for (int i = 0; i < 5; i++){
        printf("%p,", arg1[i]);
    }
    printf("]\n");

    printf("arg2: [");
    for (int i = 0; i < 5; i++){
        printf("%p,", arg2[i]);
    }
    printf("]\n");

    printf("out: [");
    for (int i = 0; i < 5; i++){
        printf("%p,", out[i]);
    }
    printf("]\n");
}