#include <stdint.h>
typedef unsigned char nathantest_uint1;
typedef signed char nathantest_int1;
#if defined(__GNUC__) || defined(__clang__)
#  define NATHANTEST_FIAT_INLINE __inline__
#else
#  define NATHANTEST_FIAT_INLINE
#endif

#if (-1 & 3) != 3
#error "This code only works on a two's complement system"
#endif

#if !defined(NATHANTEST_NO_ASM) && (defined(__GNUC__) || defined(__clang__))
static __inline__ uint32_t nathantest_value_barrier_u32(uint32_t a) {
  __asm__("" : "+r"(a) : /* no inputs */);
  return a;
}
#else
#  define nathantest_value_barrier_u32(x) (x)
#endif

/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static NATHANTEST_FIAT_INLINE void nathantest_one_redc_25519(uint64_t out1[4], const uint64_t arg1[4], uint64_t arg2, const uint64_t arg3[4]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  uint64_t x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  uint64_t x15;
  uint64_t x16;
  uint64_t x17;
  uint64_t x18;
  uint64_t x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  uint64_t x32;
  uint64_t x33;
  uint64_t x34;
  uint64_t x35;
  uint64_t x36;
  uint64_t x37;
  uint64_t x38;
  uint64_t x39;
  uint64_t x40;
  uint64_t x41;
  uint64_t x42;
  uint64_t x43;
  uint64_t x44;
  uint64_t x45;
  uint64_t x46;
  uint64_t x47;
  nathantest_mulx_u64(&x1, &x2, arg2, (arg3[2]));
  nathantest_mulx_u64(&x3, &x4, arg2, (arg3[1]));
  nathantest_mulx_u64(&x5, &x6, arg2, (arg3[0]));
  nathantest_addcarryx_u64(&x7, &x8, 0x0, x6, x3);
  nathantest_addcarryx_u64(&x9, &x10, x8, x4, x1);
  nathantest_addcarryx_u64(&x11, &x12, 0x0, (arg1[0]), x5);
  nathantest_addcarryx_u64(&x13, &x14, x12, (arg1[1]), x7);
  nathantest_addcarryx_u64(&x15, &x16, x14, (arg1[2]), x9);
  nathantest_mulx_u64(&x17, &x18, arg2, (arg3[3]));
  nathantest_addcarryx_u64(&x19, &x20, x10, x2, x17);
  nathantest_addcarryx_u64(&x21, &x22, x16, (arg1[3]), x19);
  nathantest_mulx_u64(&x23, &x24, x11, UINT64_C(0x86bca1af286bca1b));
  nathantest_mulx_u64(&x25, &x26, x23, UINT64_C(0x7fffffffffffffff));
  nathantest_mulx_u64(&x27, &x28, x23, UINT64_C(0xffffffffffffffff));
  nathantest_mulx_u64(&x29, &x30, x23, UINT64_C(0xffffffffffffffff));
  nathantest_mulx_u64(&x31, &x32, x23, UINT64_C(0xffffffffffffffed));
  nathantest_addcarryx_u64(&x33, &x34, 0x0, x32, x29);
  nathantest_addcarryx_u64(&x35, &x36, x34, x30, x27);
  nathantest_addcarryx_u64(&x37, &x38, x36, x28, x25);
  nathantest_addcarryx_u64(&x39, &x40, 0x0, x11, x31);
  nathantest_addcarryx_u64(&x41, &x42, x40, x13, x33);
  nathantest_addcarryx_u64(&x43, &x44, x42, x15, x35);
  nathantest_addcarryx_u64(&x45, &x46, x44, x21, x37);
  x47 = ((x46 + x22) + (x38 + x26));
  out1[0] = x41;
  out1[1] = x43;
  out1[2] = x45;
  out1[3] = x47;
}

static NATHANTEST_FIAT_INLINE void nathantest_redc_25519(uint64_t out1[4], const uint64_t arg2[], const int size, const uint64_t arg3[4]){
  out1 = {0,0,0,0};
  uint64_t temp[4];
  for (int i = 0; i < size; i++){
    for (int j = 0; j < 4; j++) {     
        temp[j] = out1[j];     
    }      
    nathantest_one_redc_25519(out1, temp, arg2[i], arg3);
  }
}

uint64_t * main(const uint64_t A[], const int size, const uint64_t B[4]){
  uint64_t out[4];
  nathantest_redc_25519(out, A, size, B);
  return out;
}
