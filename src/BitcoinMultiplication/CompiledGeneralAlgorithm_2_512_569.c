#include <stdint.h>
#include <stdio.h>
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
 *   arg1: [[0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x1fffffffffffffe]]
 *   arg2: [[0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x1fffffffffffffe]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x3fffffffffffffe], [0x0 ~> 0x1fffffffffffffe]]
 */
static FIAT_FIAT_INLINE void bitcoin_mul_u64(uint64_t out1[9], const uint64_t arg1[9], const uint64_t arg2[9]) {
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
  fiat_uint128 x12;
  fiat_uint128 x13;
  fiat_uint128 x14;
  fiat_uint128 x15;
  fiat_uint128 x16;
  fiat_uint128 x17;
  fiat_uint128 x18;
  fiat_uint128 x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  x1 = ((fiat_uint128)(arg1[8]) * (arg2[8]));
  x2 = (((fiat_uint128)(uint64_t)(x1 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + (((((((((fiat_uint128)(arg1[7]) * (arg2[0])) + ((fiat_uint128)(arg1[6]) * (arg2[1]))) + ((fiat_uint128)(arg1[5]) * (arg2[2]))) + ((fiat_uint128)(arg1[4]) * (arg2[3]))) + ((fiat_uint128)(arg1[3]) * (arg2[4]))) + ((fiat_uint128)(arg1[2]) * (arg2[5]))) + ((fiat_uint128)(arg1[1]) * (arg2[6]))) + ((fiat_uint128)(arg1[0]) * (arg2[7]))));
  x3 = (((fiat_uint128)(uint64_t)(x1 >> 57) * UINT16_C(0x472)) + ((uint64_t)(x2 >> 57) + ((((((((((fiat_uint128)(arg1[8]) * (arg2[0])) + ((fiat_uint128)(arg1[7]) * (arg2[1]))) + ((fiat_uint128)(arg1[6]) * (arg2[2]))) + ((fiat_uint128)(arg1[5]) * (arg2[3]))) + ((fiat_uint128)(arg1[4]) * (arg2[4]))) + ((fiat_uint128)(arg1[3]) * (arg2[5]))) + ((fiat_uint128)(arg1[2]) * (arg2[6]))) + ((fiat_uint128)(arg1[1]) * (arg2[7]))) + ((fiat_uint128)(arg1[0]) * (arg2[8])))));
  x4 = (uint64_t)(x3 & UINT64_C(0x1ffffffffffffff));
  x5 = ((uint64_t)(x3 >> 57) + (((((((((fiat_uint128)(arg1[8]) * (arg2[1])) + ((fiat_uint128)(arg1[7]) * (arg2[2]))) + ((fiat_uint128)(arg1[6]) * (arg2[3]))) + ((fiat_uint128)(arg1[5]) * (arg2[4]))) + ((fiat_uint128)(arg1[4]) * (arg2[5]))) + ((fiat_uint128)(arg1[3]) * (arg2[6]))) + ((fiat_uint128)(arg1[2]) * (arg2[7]))) + ((fiat_uint128)(arg1[1]) * (arg2[8]))));
  x6 = (((fiat_uint128)((x4 >> 56) + ((uint64_t)(x5 & UINT64_C(0x1ffffffffffffff)) * 0x2)) * UINT16_C(0x239)) + ((fiat_uint128)(arg1[0]) * (arg2[0])));
  x7 = ((uint64_t)(x5 >> 57) + ((((((((fiat_uint128)(arg1[8]) * (arg2[2])) + ((fiat_uint128)(arg1[7]) * (arg2[3]))) + ((fiat_uint128)(arg1[6]) * (arg2[4]))) + ((fiat_uint128)(arg1[5]) * (arg2[5]))) + ((fiat_uint128)(arg1[4]) * (arg2[6]))) + ((fiat_uint128)(arg1[3]) * (arg2[7]))) + ((fiat_uint128)(arg1[2]) * (arg2[8]))));
  x8 = (((fiat_uint128)(uint64_t)(x7 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x6 >> 57) + (((fiat_uint128)(arg1[1]) * (arg2[0])) + ((fiat_uint128)(arg1[0]) * (arg2[1])))));
  x9 = ((uint64_t)(x7 >> 57) + (((((((fiat_uint128)(arg1[8]) * (arg2[3])) + ((fiat_uint128)(arg1[7]) * (arg2[4]))) + ((fiat_uint128)(arg1[6]) * (arg2[5]))) + ((fiat_uint128)(arg1[5]) * (arg2[6]))) + ((fiat_uint128)(arg1[4]) * (arg2[7]))) + ((fiat_uint128)(arg1[3]) * (arg2[8]))));
  x10 = (((fiat_uint128)(uint64_t)(x9 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x8 >> 57) + ((((fiat_uint128)(arg1[2]) * (arg2[0])) + ((fiat_uint128)(arg1[1]) * (arg2[1]))) + ((fiat_uint128)(arg1[0]) * (arg2[2])))));
  x11 = ((uint64_t)(x9 >> 57) + ((((((fiat_uint128)(arg1[8]) * (arg2[4])) + ((fiat_uint128)(arg1[7]) * (arg2[5]))) + ((fiat_uint128)(arg1[6]) * (arg2[6]))) + ((fiat_uint128)(arg1[5]) * (arg2[7]))) + ((fiat_uint128)(arg1[4]) * (arg2[8]))));
  x12 = (((fiat_uint128)(uint64_t)(x11 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x10 >> 57) + (((((fiat_uint128)(arg1[3]) * (arg2[0])) + ((fiat_uint128)(arg1[2]) * (arg2[1]))) + ((fiat_uint128)(arg1[1]) * (arg2[2]))) + ((fiat_uint128)(arg1[0]) * (arg2[3])))));
  x13 = ((uint64_t)(x11 >> 57) + (((((fiat_uint128)(arg1[8]) * (arg2[5])) + ((fiat_uint128)(arg1[7]) * (arg2[6]))) + ((fiat_uint128)(arg1[6]) * (arg2[7]))) + ((fiat_uint128)(arg1[5]) * (arg2[8]))));
  x14 = (((fiat_uint128)(uint64_t)(x13 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x12 >> 57) + ((((((fiat_uint128)(arg1[4]) * (arg2[0])) + ((fiat_uint128)(arg1[3]) * (arg2[1]))) + ((fiat_uint128)(arg1[2]) * (arg2[2]))) + ((fiat_uint128)(arg1[1]) * (arg2[3]))) + ((fiat_uint128)(arg1[0]) * (arg2[4])))));
  x15 = ((uint64_t)(x13 >> 57) + ((((fiat_uint128)(arg1[8]) * (arg2[6])) + ((fiat_uint128)(arg1[7]) * (arg2[7]))) + ((fiat_uint128)(arg1[6]) * (arg2[8]))));
  x16 = (((fiat_uint128)(uint64_t)(x15 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x14 >> 57) + (((((((fiat_uint128)(arg1[5]) * (arg2[0])) + ((fiat_uint128)(arg1[4]) * (arg2[1]))) + ((fiat_uint128)(arg1[3]) * (arg2[2]))) + ((fiat_uint128)(arg1[2]) * (arg2[3]))) + ((fiat_uint128)(arg1[1]) * (arg2[4]))) + ((fiat_uint128)(arg1[0]) * (arg2[5])))));
  x17 = ((uint64_t)(x15 >> 57) + (((fiat_uint128)(arg1[8]) * (arg2[7])) + ((fiat_uint128)(arg1[7]) * (arg2[8]))));
  x18 = (((fiat_uint128)(uint64_t)(x17 & UINT64_C(0x1ffffffffffffff)) * UINT16_C(0x472)) + ((uint64_t)(x16 >> 57) + ((((((((fiat_uint128)(arg1[6]) * (arg2[0])) + ((fiat_uint128)(arg1[5]) * (arg2[1]))) + ((fiat_uint128)(arg1[4]) * (arg2[2]))) + ((fiat_uint128)(arg1[3]) * (arg2[3]))) + ((fiat_uint128)(arg1[2]) * (arg2[4]))) + ((fiat_uint128)(arg1[1]) * (arg2[5]))) + ((fiat_uint128)(arg1[0]) * (arg2[6])))));
  x19 = (((fiat_uint128)(uint64_t)(x17 >> 57) * UINT16_C(0x472)) + ((uint64_t)(x18 >> 57) + (uint64_t)(x2 & UINT64_C(0x1ffffffffffffff))));
  x20 = (uint64_t)(x6 & UINT64_C(0x1ffffffffffffff));
  x21 = (uint64_t)(x8 & UINT64_C(0x1ffffffffffffff));
  x22 = (uint64_t)(x10 & UINT64_C(0x1ffffffffffffff));
  x23 = (uint64_t)(x12 & UINT64_C(0x1ffffffffffffff));
  x24 = (uint64_t)(x14 & UINT64_C(0x1ffffffffffffff));
  x25 = (uint64_t)(x16 & UINT64_C(0x1ffffffffffffff));
  x26 = (uint64_t)(x18 & UINT64_C(0x1ffffffffffffff));
  x27 = (uint64_t)(x19 & UINT64_C(0x1ffffffffffffff));
  x28 = ((uint64_t)(x19 >> 57) + (x4 & UINT64_C(0xffffffffffffff)));
  out1[0] = x20;
  out1[1] = x21;
  out1[2] = x22;
  out1[3] = x23;
  out1[4] = x24;
  out1[5] = x25;
  out1[6] = x26;
  out1[7] = x27;
  out1[8] = x28;
}



int main() {
    srand(time(NULL));

    uint64_t arg1[9] = {rand(), rand(), rand(), rand(), rand(), rand(), rand(), rand(), rand()};
    uint64_t arg2[9] = {rand(), rand(), rand(), rand(), rand(), rand(), rand(), rand(), rand()};
    uint64_t out[9];

    bitcoin_mul_u64(out, arg1, arg2);
    
    printf("arg1: [");
    for (int i = 0; i < 9; i++){
        printf("%p,", arg1[i]);
    }
    printf("]\n");

    printf("arg2: [");
    for (int i = 0; i < 9; i++){
        printf("%p,", arg2[i]);
    }
    printf("]\n");

    printf("out: [");
    for (int i = 0; i < 9; i++){
        printf("%p,", out[i]);
    }
    printf("]\n");
}



