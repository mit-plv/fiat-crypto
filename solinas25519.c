#include <stdint.h>
#include <stdio.h>
typedef unsigned char fiat_p25519_uint1;
typedef signed char fiat_p25519_int1;
#if defined(__GNUC__) || defined(__clang__)
#  define FIAT_P25519_FIAT_EXTENSION __extension__
#  define FIAT_P25519_FIAT_INLINE __inline__
#else
#  define FIAT_P25519_FIAT_EXTENSION
#  define FIAT_P25519_FIAT_INLINE
#endif

FIAT_P25519_FIAT_EXTENSION typedef signed __int128 fiat_p25519_int128;
FIAT_P25519_FIAT_EXTENSION typedef unsigned __int128 fiat_p25519_uint128;

#if (-1 & 3) != 3
#error "This code only works on a two's complement system"
#endif

#if !defined(FIAT_P25519_NO_ASM) && (defined(__GNUC__) || defined(__clang__))
static __inline__ uint64_t fiat_p25519_value_barrier_u64(uint64_t a) {
  __asm__("" : "+r"(a) : /* no inputs */);
  return a;
}
#else
#  define fiat_p25519_value_barrier_u64(x) (x)
#endif

static FIAT_P25519_FIAT_INLINE void fiat_p25519_addcarryx_u64(uint64_t* out1, fiat_p25519_uint1* out2, fiat_p25519_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  fiat_p25519_uint128 x1;
  uint64_t x2;
  fiat_p25519_uint1 x3;
  x1 = ((arg1 + (fiat_p25519_uint128)arg2) + arg3);
  x2 = (uint64_t)(x1 & UINT64_C(0xffffffffffffffff));
  x3 = (fiat_p25519_uint1)(x1 >> 64);
  *out1 = x2;
  *out2 = x3;
}

static FIAT_P25519_FIAT_INLINE void fiat_p25519_mulx_u64(uint64_t* out1, uint64_t* out2, uint64_t arg1, uint64_t arg2) {
  fiat_p25519_uint128 x1;
  uint64_t x2;
  uint64_t x3;
  x1 = ((fiat_p25519_uint128)arg1 * arg2);
  x2 = (uint64_t)(x1 & UINT64_C(0xffffffffffffffff));
  x3 = (uint64_t)(x1 >> 64);
  *out1 = x2;
  *out2 = x3;
}

static FIAT_P25519_FIAT_INLINE void fiat_p25519_mul(uint64_t out1[4], const uint64_t arg1[4], const uint64_t arg2[4]) {
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
  fiat_p25519_uint1 x34;
  uint64_t x35;
  fiat_p25519_uint1 x36;
  uint64_t x37;
  uint64_t x38;
  fiat_p25519_uint1 x39;
  uint64_t x40;
  fiat_p25519_uint1 x41;
  uint64_t x42;
  fiat_p25519_uint1 x43;
  uint64_t x44;
  uint64_t x45;
  fiat_p25519_uint1 x46;
  uint64_t x47;
  fiat_p25519_uint1 x48;
  uint64_t x49;
  fiat_p25519_uint1 x50;
  uint64_t x51;
  fiat_p25519_uint1 x52;
  uint64_t x53;
  fiat_p25519_uint1 x54;
  uint64_t x55;
  uint64_t x56;
  fiat_p25519_uint1 x57;
  uint64_t x58;
  fiat_p25519_uint1 x59;
  uint64_t x60;
  fiat_p25519_uint1 x61;
  uint64_t x62;
  fiat_p25519_uint1 x63;
  uint64_t x64;
  fiat_p25519_uint1 x65;
  uint64_t x66;
  fiat_p25519_uint1 x67;
  uint64_t x68;
  fiat_p25519_uint1 x69;
  uint64_t x70;
  fiat_p25519_uint1 x71;
  uint64_t x72;
  fiat_p25519_uint1 x73;
  uint64_t x74;
  fiat_p25519_uint1 x75;
  uint64_t x76;
  fiat_p25519_uint1 x77;
  uint64_t x78;
  fiat_p25519_uint1 x79;
  uint64_t x80;
  fiat_p25519_uint1 x81;
  uint64_t x82;
  fiat_p25519_uint1 x83;
  uint64_t x84;
  fiat_p25519_uint1 x85;
  uint64_t x86;
  fiat_p25519_uint1 x87;
  uint64_t x88;
  fiat_p25519_uint1 x89;
  uint64_t x90;
  fiat_p25519_uint1 x91;
  uint64_t x92;
  fiat_p25519_uint1 x93;
  uint64_t x94;
  fiat_p25519_uint1 x95;
  uint64_t x96;
  uint64_t x97;
  uint64_t x98;
  uint64_t x99;
  uint64_t x100;
  uint64_t x101;
  uint64_t x102;
  fiat_p25519_uint1 x103;
  uint64_t x104;
  fiat_p25519_uint1 x105;
  uint64_t x106;
  uint64_t x107;
  uint64_t x108;
  fiat_p25519_uint1 x109;
  uint64_t x110;
  uint64_t x111;
  uint64_t x112;
  uint64_t x113;
  fiat_p25519_uint1 x114;
  uint64_t x115;
  fiat_p25519_uint1 x116;
  uint64_t x117;
  fiat_p25519_uint1 x118;
  uint64_t x119;
  fiat_p25519_uint1 x120;
  uint64_t x121;
  uint64_t x122;
  uint64_t x123;
  uint64_t x124;
  fiat_p25519_uint1 x125;
  uint64_t x126;
  fiat_p25519_uint1 x127;
  uint64_t x128;
  fiat_p25519_uint1 x129;
  uint64_t x130;
  fiat_p25519_uint1 x131;
  uint64_t x132;
  uint64_t x133;
  uint64_t x134;
  fiat_p25519_uint1 x135;
  uint64_t x136;
  fiat_p25519_uint1 x137;
  uint64_t x138;
  fiat_p25519_uint1 x139;
  uint64_t x140;
  fiat_p25519_uint1 x141;
  fiat_p25519_mulx_u64(&x1, &x2, (arg1[3]), (arg2[3]));
  fiat_p25519_mulx_u64(&x3, &x4, (arg1[3]), (arg2[2]));
  fiat_p25519_mulx_u64(&x5, &x6, (arg1[3]), (arg2[1]));
  fiat_p25519_mulx_u64(&x7, &x8, (arg1[3]), (arg2[0]));
  fiat_p25519_mulx_u64(&x9, &x10, (arg1[2]), (arg2[3]));
  fiat_p25519_mulx_u64(&x11, &x12, (arg1[2]), (arg2[2]));
  fiat_p25519_mulx_u64(&x13, &x14, (arg1[2]), (arg2[1]));
  fiat_p25519_mulx_u64(&x15, &x16, (arg1[2]), (arg2[0]));
  fiat_p25519_mulx_u64(&x17, &x18, (arg1[1]), (arg2[3]));
  fiat_p25519_mulx_u64(&x19, &x20, (arg1[1]), (arg2[2]));
  fiat_p25519_mulx_u64(&x21, &x22, (arg1[1]), (arg2[1]));
  fiat_p25519_mulx_u64(&x23, &x24, (arg1[1]), (arg2[0]));
  fiat_p25519_mulx_u64(&x25, &x26, (arg1[0]), (arg2[3]));
  fiat_p25519_mulx_u64(&x27, &x28, (arg1[0]), (arg2[2]));
  fiat_p25519_mulx_u64(&x29, &x30, (arg1[0]), (arg2[1]));
  fiat_p25519_mulx_u64(&x31, &x32, (arg1[0]), (arg2[0]));
  fiat_p25519_addcarryx_u64(&x33, &x34, 0x0, x28, x7);
  fiat_p25519_addcarryx_u64(&x35, &x36, x34, x26, x5);
  x37 = (x36 + x18);
  fiat_p25519_addcarryx_u64(&x38, &x39, 0x0, x33, x13);
  fiat_p25519_addcarryx_u64(&x40, &x41, x39, x35, x8);
  fiat_p25519_addcarryx_u64(&x42, &x43, x41, x37, 0x0);
  x44 = (x43 + x10);
  fiat_p25519_addcarryx_u64(&x45, &x46, 0x0, x30, x15);
  fiat_p25519_addcarryx_u64(&x47, &x48, x46, x38, x16);
  fiat_p25519_addcarryx_u64(&x49, &x50, x48, x40, x11);
  fiat_p25519_addcarryx_u64(&x51, &x52, x50, x42, x3);
  fiat_p25519_addcarryx_u64(&x53, &x54, x52, x44, 0x0);
  x55 = (x54 + x2);
  fiat_p25519_addcarryx_u64(&x56, &x57, 0x0, x45, x21);
  fiat_p25519_addcarryx_u64(&x58, &x59, x57, x47, x19);
  fiat_p25519_addcarryx_u64(&x60, &x61, x59, x49, x14);
  fiat_p25519_addcarryx_u64(&x62, &x63, x61, x51, x6);
  fiat_p25519_addcarryx_u64(&x64, &x65, x63, x53, 0x0);
  fiat_p25519_addcarryx_u64(&x66, &x67, x65, x55, 0x0);
  fiat_p25519_addcarryx_u64(&x68, &x69, 0x0, x32, x23);
  fiat_p25519_addcarryx_u64(&x70, &x71, x69, x56, x24);
  fiat_p25519_addcarryx_u64(&x72, &x73, x71, x58, x22);
  fiat_p25519_addcarryx_u64(&x74, &x75, x73, x60, x17);
  fiat_p25519_addcarryx_u64(&x76, &x77, x75, x62, x9);
  fiat_p25519_addcarryx_u64(&x78, &x79, x77, x64, x1);
  fiat_p25519_addcarryx_u64(&x80, &x81, x79, x66, 0x0);
  fiat_p25519_addcarryx_u64(&x82, &x83, 0x0, x68, x29);
  fiat_p25519_addcarryx_u64(&x84, &x85, x83, x70, x27);
  fiat_p25519_addcarryx_u64(&x86, &x87, x85, x72, x25);
  fiat_p25519_addcarryx_u64(&x88, &x89, x87, x74, x20);
  fiat_p25519_addcarryx_u64(&x90, &x91, x89, x76, x12);
  fiat_p25519_addcarryx_u64(&x92, &x93, x91, x78, x4);
  fiat_p25519_addcarryx_u64(&x94, &x95, x93, x80, 0x0);
  fiat_p25519_mulx_u64(&x96, &x97, UINT8_C(0x26), x92);
  fiat_p25519_mulx_u64(&x98, &x99, UINT8_C(0x26), x90);
  fiat_p25519_mulx_u64(&x100, &x101, UINT8_C(0x26), x88);
  fiat_p25519_addcarryx_u64(&x102, &x103, 0x0, x82, x98);
  fiat_p25519_addcarryx_u64(&x104, &x105, x103, x84, x96);
  fiat_p25519_mulx_u64(&x106, &x107, UINT8_C(0x26), x94);
  fiat_p25519_addcarryx_u64(&x108, &x109, x105, x86, x106);
  fiat_p25519_mulx_u64(&x110, &x111, UINT8_C(0x26), x94);
  x112 = (x109 + x111);
  fiat_p25519_addcarryx_u64(&x113, &x114, 0x0, x31, x100);
  fiat_p25519_addcarryx_u64(&x115, &x116, x114, x102, x101);
  fiat_p25519_addcarryx_u64(&x117, &x118, x116, x104, x99);
  fiat_p25519_addcarryx_u64(&x119, &x120, x118, x108, x97);
  x121 = (x120 + x112);
  fiat_p25519_mulx_u64(&x122, &x123, UINT8_C(0x26), x121);
  fiat_p25519_addcarryx_u64(&x124, &x125, 0x0, x113, x122);
  fiat_p25519_addcarryx_u64(&x126, &x127, x125, x115, 0x0);
  fiat_p25519_addcarryx_u64(&x128, &x129, x127, x117, 0x0);
  fiat_p25519_addcarryx_u64(&x130, &x131, x129, x119, 0x0);
  fiat_p25519_mulx_u64(&x132, &x133, UINT8_C(0x26), x131);
  fiat_p25519_addcarryx_u64(&x134, &x135, 0x0, x124, x132);
  fiat_p25519_addcarryx_u64(&x136, &x137, x135, x126, 0x0);
  fiat_p25519_addcarryx_u64(&x138, &x139, x137, x128, 0x0);
  fiat_p25519_addcarryx_u64(&x140, &x141, x139, x130, 0x0);
  out1[0] = x134;
  out1[1] = x136;
  out1[2] = x138;
  out1[3] = x140;
}

int main() {
  uint64_t arg1[4] = {0};
  uint64_t arg2[4] = {0};
  for (int i = 0; i < 4; i++) {
    arg1[i] = 0xffffffffffffffff;
    arg2[i] = 0xffffffffffffffff;
  }
  uint64_t out1[4] = {0};
  fiat_p25519_mul(out1, arg1, arg2);
  for (int i = 0; i < 4; i++) {
    printf("%d ", out1[i]);
  }
  printf("\n");
  return 0;
}
