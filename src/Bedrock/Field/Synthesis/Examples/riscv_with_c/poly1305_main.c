//#include "int.h"
//#include "str.h"
#include <stdio.h>
#include <stdint.h>
//typedef uint8_t UINT8_C;
//typedef uint32_t UINT32_C;

typedef unsigned char poly1305_uint1;
typedef signed char poly1305_int1;

// TODO
#define CRYPTO_memcmp memcmp

// TODO: make sure these are actually explicit
void *explicit_memcpy(void *dest, const void *src, size_t n) {
  for (size_t i = 0; i < n; i++) {
    ((uint8_t *) dest)[i] = ((uint8_t *) src)[i];
  }
  return dest;
}

void explicit_memzero(void *dest, size_t n) {
  for (size_t i = 0; i < n; i++) {
    ((uint8_t *) dest)[i] = 0;
  }
}

extern void poly1305_addcarryx_u26(uint32_t* out1, poly1305_uint1* out2, poly1305_uint1 arg1, uint32_t arg2, uint32_t arg3);
extern void poly1305_subborrowx_u26(uint32_t* out1, poly1305_uint1* out2, poly1305_uint1 arg1, uint32_t arg2, uint32_t arg3);
extern void poly1305_cmovznz_u32(uint32_t* out1, poly1305_uint1 arg1, uint32_t arg2, uint32_t arg3);
extern void poly1305_carry_mul(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]);
extern void poly1305_carry_square(uint32_t out1[5], const uint32_t arg1[5]);
extern void poly1305_carry(uint32_t out1[5], const uint32_t arg1[5]);
extern void poly1305_add(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]);
extern void poly1305_sub(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]);
extern void poly1305_opp(uint32_t out1[5], const uint32_t arg1[5]);
extern void poly1305_selectznz(uint32_t out1[5], poly1305_uint1 arg1, const uint32_t arg2[5], const uint32_t arg3[5]);
extern void poly1305_to_bytes(uint8_t out1[17], const uint32_t arg1[5]);
extern void poly1305_from_bytes(uint32_t out1[5], const uint8_t arg1[17]);

static void print16(unsigned char out[16]) {
        for (int i = 0; i < 16; i++) {
                printf("%02x ", out[i]);
        }
        printf("\n");
}


#include <stdint.h>
#include <memory.h>


// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_carry_mul(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]) {
  poly1305_carry_mul((uintptr_t)out1, (uintptr_t)arg1, (uintptr_t)arg2);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_carry_square(uint32_t out1[5], const uint32_t arg1[5]) {
  poly1305_carry_square((uintptr_t)out1, (uintptr_t)arg1);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_carry(uint32_t out1[5], const uint32_t arg1[5]) {
  poly1305_carry((uintptr_t)out1, (uintptr_t)arg1);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_add(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]) {
  poly1305_add((uintptr_t)out1, (uintptr_t)arg1, (uintptr_t)arg2);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_sub(uint32_t out1[5], const uint32_t arg1[5], const uint32_t arg2[5]) {
  poly1305_sub((uintptr_t)out1, (uintptr_t)arg1, (uintptr_t)arg2);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_opp(uint32_t out1[5], const uint32_t arg1[5]) {
  poly1305_opp((uintptr_t)out1, (uintptr_t)arg1);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_selectznz(uint32_t out1[5], uint8_t arg1, const uint32_t arg2[5], const uint32_t arg3[5]) {
  poly1305_selectznz((uintptr_t)out1, (uintptr_t)arg1, (uintptr_t)arg2, (uintptr_t)arg3);
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 */
static
void internal_fiat_poly1305_to_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x0, x6, x5, x1, x8, x9, x10, x12, x13, x11, x2, x15, x16, x17, x19, x20, x18, x3, x22, x23, x24, x26, x27, x25, x4, x29, x30, x31, x33, x34, x32, x36, x7, x38, x39, x41, x14, x42, x43, x45, x44, x46, x48, x21, x49, x50, x52, x51, x53, x55, x28, x56, x57, x59, x58, x60, x62, x35, x63, x37, x64, x61, x54, x47, x40, x70, x72, x68, x74, x75, x77, x79, x67, x81, x82, x84, x86, x66, x88, x89, x91, x93, x65, x97, x99, x69, x71, x73, x76, x78, x80, x83, x85, x87, x90, x92, x94, x95, x96, x98, x100, x101, x102, x103, x104, x105, x106, x107, x108, x109, x110, x111, x112, x113, x114, x115, x116, x117, x118;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), sizeof(uintptr_t));
  x1 = _br2_load((in0)+((uintptr_t)4ULL), sizeof(uintptr_t));
  x2 = _br2_load((in0)+((uintptr_t)8ULL), sizeof(uintptr_t));
  x3 = _br2_load((in0)+((uintptr_t)12ULL), sizeof(uintptr_t));
  x4 = _br2_load((in0)+((uintptr_t)16ULL), sizeof(uintptr_t));
  /*skip*/
  /*skip*/
  x5 = (x0)-((uintptr_t)67108859ULL);
  x6 = (x0)<(x5);
  x7 = (x5)&((uintptr_t)67108863ULL);
  x8 = ((x6)<<((uintptr_t)6ULL))-((x5)>>((uintptr_t)26ULL));
  x9 = (x1)-((uintptr_t)67108863ULL);
  x10 = (x1)<(x9);
  x11 = (x9)-(x8);
  x12 = (x9)<(x11);
  x13 = (x10)+(x12);
  x14 = (x11)&((uintptr_t)67108863ULL);
  x15 = ((x13)<<((uintptr_t)6ULL))-((x11)>>((uintptr_t)26ULL));
  x16 = (x2)-((uintptr_t)67108863ULL);
  x17 = (x2)<(x16);
  x18 = (x16)-(x15);
  x19 = (x16)<(x18);
  x20 = (x17)+(x19);
  x21 = (x18)&((uintptr_t)67108863ULL);
  x22 = ((x20)<<((uintptr_t)6ULL))-((x18)>>((uintptr_t)26ULL));
  x23 = (x3)-((uintptr_t)67108863ULL);
  x24 = (x3)<(x23);
  x25 = (x23)-(x22);
  x26 = (x23)<(x25);
  x27 = (x24)+(x26);
  x28 = (x25)&((uintptr_t)67108863ULL);
  x29 = ((x27)<<((uintptr_t)6ULL))-((x25)>>((uintptr_t)26ULL));
  x30 = (x4)-((uintptr_t)67108863ULL);
  x31 = (x4)<(x30);
  x32 = (x30)-(x29);
  x33 = (x30)<(x32);
  x34 = (x31)+(x33);
  x35 = (x32)&((uintptr_t)67108863ULL);
  x36 = ((x34)<<((uintptr_t)6ULL))-((x32)>>((uintptr_t)26ULL));
  x37 = ((uintptr_t)-1ULL)+((x36)==((uintptr_t)0ULL));
  x38 = (x7)+((x37)&((uintptr_t)67108859ULL));
  x39 = (x38)<(x7);
  x40 = (x38)&((uintptr_t)67108863ULL);
  x41 = ((x38)>>((uintptr_t)26ULL))+((x39)<<((uintptr_t)6ULL));
  x42 = (x41)+(x14);
  x43 = (x42)<(x14);
  x44 = (x42)+((x37)&((uintptr_t)67108863ULL));
  x45 = (x44)<((x37)&((uintptr_t)67108863ULL));
  x46 = (x43)+(x45);
  x47 = (x44)&((uintptr_t)67108863ULL);
  x48 = ((x44)>>((uintptr_t)26ULL))+((x46)<<((uintptr_t)6ULL));
  x49 = (x48)+(x21);
  x50 = (x49)<(x21);
  x51 = (x49)+((x37)&((uintptr_t)67108863ULL));
  x52 = (x51)<((x37)&((uintptr_t)67108863ULL));
  x53 = (x50)+(x52);
  x54 = (x51)&((uintptr_t)67108863ULL);
  x55 = ((x51)>>((uintptr_t)26ULL))+((x53)<<((uintptr_t)6ULL));
  x56 = (x55)+(x28);
  x57 = (x56)<(x28);
  x58 = (x56)+((x37)&((uintptr_t)67108863ULL));
  x59 = (x58)<((x37)&((uintptr_t)67108863ULL));
  x60 = (x57)+(x59);
  x61 = (x58)&((uintptr_t)67108863ULL);
  x62 = ((x58)>>((uintptr_t)26ULL))+((x60)<<((uintptr_t)6ULL));
  x63 = (x62)+(x35);
  x64 = (x63)+((x37)&((uintptr_t)67108863ULL));
  x65 = (x64)&((uintptr_t)67108863ULL);
  x66 = (x61)<<((uintptr_t)6ULL);
  x67 = (x54)<<((uintptr_t)4ULL);
  x68 = (x47)<<((uintptr_t)2ULL);
  x69 = (x40)&((uintptr_t)255ULL);
  x70 = (x40)>>((uintptr_t)8ULL);
  x71 = (x70)&((uintptr_t)255ULL);
  x72 = (x70)>>((uintptr_t)8ULL);
  x73 = (x72)&((uintptr_t)255ULL);
  x74 = (x72)>>((uintptr_t)8ULL);
  x75 = (x68)+(x74);
  x76 = (x75)&((uintptr_t)255ULL);
  x77 = (x75)>>((uintptr_t)8ULL);
  x78 = (x77)&((uintptr_t)255ULL);
  x79 = (x77)>>((uintptr_t)8ULL);
  x80 = (x79)&((uintptr_t)255ULL);
  x81 = (x79)>>((uintptr_t)8ULL);
  x82 = (x67)+(x81);
  x83 = (x82)&((uintptr_t)255ULL);
  x84 = (x82)>>((uintptr_t)8ULL);
  x85 = (x84)&((uintptr_t)255ULL);
  x86 = (x84)>>((uintptr_t)8ULL);
  x87 = (x86)&((uintptr_t)255ULL);
  x88 = (x86)>>((uintptr_t)8ULL);
  x89 = (x66)+(x88);
  x90 = (x89)&((uintptr_t)255ULL);
  x91 = (x89)>>((uintptr_t)8ULL);
  x92 = (x91)&((uintptr_t)255ULL);
  x93 = (x91)>>((uintptr_t)8ULL);
  x94 = (x93)&((uintptr_t)255ULL);
  x95 = (x93)>>((uintptr_t)8ULL);
  x96 = (x65)&((uintptr_t)255ULL);
  x97 = (x65)>>((uintptr_t)8ULL);
  x98 = (x97)&((uintptr_t)255ULL);
  x99 = (x97)>>((uintptr_t)8ULL);
  x100 = (x99)&((uintptr_t)255ULL);
  x101 = (x99)>>((uintptr_t)8ULL);
  x102 = x69;
  x103 = x71;
  x104 = x73;
  x105 = x76;
  x106 = x78;
  x107 = x80;
  x108 = x83;
  x109 = x85;
  x110 = x87;
  x111 = x90;
  x112 = x92;
  x113 = x94;
  x114 = x95;
  x115 = x96;
  x116 = x98;
  x117 = x100;
  x118 = x101;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x102, 1);
  _br2_store((out0)+((uintptr_t)1ULL), x103, 1);
  _br2_store((out0)+((uintptr_t)2ULL), x104, 1);
  _br2_store((out0)+((uintptr_t)3ULL), x105, 1);
  _br2_store((out0)+((uintptr_t)4ULL), x106, 1);
  _br2_store((out0)+((uintptr_t)5ULL), x107, 1);
  _br2_store((out0)+((uintptr_t)6ULL), x108, 1);
  _br2_store((out0)+((uintptr_t)7ULL), x109, 1);
  _br2_store((out0)+((uintptr_t)8ULL), x110, 1);
  _br2_store((out0)+((uintptr_t)9ULL), x111, 1);
  _br2_store((out0)+((uintptr_t)10ULL), x112, 1);
  _br2_store((out0)+((uintptr_t)11ULL), x113, 1);
  _br2_store((out0)+((uintptr_t)12ULL), x114, 1);
  _br2_store((out0)+((uintptr_t)13ULL), x115, 1);
  _br2_store((out0)+((uintptr_t)14ULL), x116, 1);
  _br2_store((out0)+((uintptr_t)15ULL), x117, 1);
  _br2_store((out0)+((uintptr_t)16ULL), x118, 1);
  /*skip*/
  return;
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_to_bytes(uint8_t out1[17], const uint32_t arg1[5]) {
  internal_fiat_poly1305_to_bytes((uintptr_t)out1, (uintptr_t)arg1);
  printf("fiat_poly1305_to_bytes: ");
  print16(out1);
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
 */
static
void internal_fiat_poly1305_from_bytes(uintptr_t out0, uintptr_t in0) {
  uintptr_t x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x32, x33, x31, x34, x30, x35, x36, x29, x38, x28, x39, x27, x40, x41, x26, x43, x25, x44, x24, x45, x46, x23, x48, x22, x49, x21, x50, x19, x20, x18, x52, x17, x53, x37, x42, x47, x51, x54, x55, x56, x57, x58, x59;
  x0 = _br2_load((in0)+((uintptr_t)0ULL), 1);
  x1 = _br2_load((in0)+((uintptr_t)1ULL), 1);
  x2 = _br2_load((in0)+((uintptr_t)2ULL), 1);
  x3 = _br2_load((in0)+((uintptr_t)3ULL), 1);
  x4 = _br2_load((in0)+((uintptr_t)4ULL), 1);
  x5 = _br2_load((in0)+((uintptr_t)5ULL), 1);
  x6 = _br2_load((in0)+((uintptr_t)6ULL), 1);
  x7 = _br2_load((in0)+((uintptr_t)7ULL), 1);
  x8 = _br2_load((in0)+((uintptr_t)8ULL), 1);
  x9 = _br2_load((in0)+((uintptr_t)9ULL), 1);
  x10 = _br2_load((in0)+((uintptr_t)10ULL), 1);
  x11 = _br2_load((in0)+((uintptr_t)11ULL), 1);
  x12 = _br2_load((in0)+((uintptr_t)12ULL), 1);
  x13 = _br2_load((in0)+((uintptr_t)13ULL), 1);
  x14 = _br2_load((in0)+((uintptr_t)14ULL), 1);
  x15 = _br2_load((in0)+((uintptr_t)15ULL), 1);
  x16 = _br2_load((in0)+((uintptr_t)16ULL), 1);
  /*skip*/
  /*skip*/
  x17 = (x16)<<((uintptr_t)24ULL);
  x18 = (x15)<<((uintptr_t)16ULL);
  x19 = (x14)<<((uintptr_t)8ULL);
  x20 = x13;
  x21 = (x12)<<((uintptr_t)18ULL);
  x22 = (x11)<<((uintptr_t)10ULL);
  x23 = (x10)<<((uintptr_t)2ULL);
  x24 = (x9)<<((uintptr_t)20ULL);
  x25 = (x8)<<((uintptr_t)12ULL);
  x26 = (x7)<<((uintptr_t)4ULL);
  x27 = (x6)<<((uintptr_t)22ULL);
  x28 = (x5)<<((uintptr_t)14ULL);
  x29 = (x4)<<((uintptr_t)6ULL);
  x30 = (x3)<<((uintptr_t)24ULL);
  x31 = (x2)<<((uintptr_t)16ULL);
  x32 = (x1)<<((uintptr_t)8ULL);
  x33 = x0;
  x34 = (x32)+(x33);
  x35 = (x31)+(x34);
  x36 = (x30)+(x35);
  x37 = (x36)&((uintptr_t)67108863ULL);
  x38 = (x36)>>((uintptr_t)26ULL);
  x39 = (x29)+(x38);
  x40 = (x28)+(x39);
  x41 = (x27)+(x40);
  x42 = (x41)&((uintptr_t)67108863ULL);
  x43 = (x41)>>((uintptr_t)26ULL);
  x44 = (x26)+(x43);
  x45 = (x25)+(x44);
  x46 = (x24)+(x45);
  x47 = (x46)&((uintptr_t)67108863ULL);
  x48 = (x46)>>((uintptr_t)26ULL);
  x49 = (x23)+(x48);
  x50 = (x22)+(x49);
  x51 = (x21)+(x50);
  x52 = (x19)+(x20);
  x53 = (x18)+(x52);
  x54 = (x17)+(x53);
  x55 = x37;
  x56 = x42;
  x57 = x47;
  x58 = x51;
  x59 = x54;
  /*skip*/
  _br2_store((out0)+((uintptr_t)0ULL), x55, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)4ULL), x56, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)8ULL), x57, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)12ULL), x58, sizeof(uintptr_t));
  _br2_store((out0)+((uintptr_t)16ULL), x59, sizeof(uintptr_t));
  /*skip*/
  return;
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_from_bytes(uint32_t out1[5], const uint8_t arg1[17]) {
  internal_fiat_poly1305_from_bytes((uintptr_t)out1, (uintptr_t)arg1);
  printf("fiat_poly1305_from_bytes: ");
  print16(out1);
}



/*
 * Poly1305 as specified in section 2.5 of RFC8439
 */
static void poly1305_mac(unsigned char mac[16], const unsigned char *msg, uint32_t msglen, unsigned char key[32]) {
        uint32_t r[5], s[5], a[5] = {0}, n[5];
        unsigned char r_bytes[17] = {0}; // 17 because poly1305_from_bytes reads 17 bytes
        unsigned char s_bytes[17] = {0};
        unsigned char mac_with_extra_byte[17] = {0};

        explicit_memcpy(r_bytes, key, 16); // First 16 bytes are r
        explicit_memcpy(s_bytes, &key[16], 16); // Second 16 bytes are s

        // clamp r
        r_bytes[3] &= 15;
        r_bytes[7] &= 15;
        r_bytes[11] &= 15;
        r_bytes[15] &= 15;
        r_bytes[4] &= 252;
        r_bytes[8] &= 252;
        r_bytes[12] &= 252;
        r_bytes[16] = 0;

        fiat_poly1305_from_bytes(r, r_bytes);
        fiat_poly1305_from_bytes(s, s_bytes);

        unsigned char block[17] = {0};
        for (uint32_t i = 0; i <= (msglen>>4); i++) {
                // From the RFC:
                // "Divide the message into 16-byte blocks; the last one might be shorter....
                // Add one bit beyond the number of octets. For a 16-byte block, this is equivalent to adding 2^128.
                // For the shorter block, it can be 2^120, 2^112, or any power of two that is evenly divisible by 8,
                // all the way down to 2^8"
                uint32_t blocklen = (i < (msglen>>4) ? 16 : msglen & 15);
                explicit_memcpy(block, msg+(i<<4), blocklen);
                block[blocklen] = 0x01;

                fiat_poly1305_from_bytes(n, block);
                explicit_memzero(block, 17);

                fiat_poly1305_add(a, n, a);
                fiat_poly1305_carry(a, a);

                fiat_poly1305_carry_mul(a, r, a);
        }
        fiat_poly1305_add(a, s, a);
        fiat_poly1305_carry(a, a);

        fiat_poly1305_to_bytes(mac_with_extra_byte, a);
        explicit_memcpy(mac, mac_with_extra_byte, 16);
        // zero r, s. a, n, and mac_with_extra_byte
        explicit_memzero(r_bytes, 17);
        explicit_memzero(s_bytes, 17);
        explicit_memzero(mac_with_extra_byte, 17);
        for (uint32_t i = 0; i < 5; i++) {
                *((volatile uint32_t*)(&r[i])) = 0;
                *((volatile uint32_t*)(&s[i])) = 0;
                *((volatile uint32_t*)(&a[i])) = 0;
                *((volatile uint32_t*)(&n[i])) = 0;
        }
}


// Test vector from RFC8439 section 2.5.2
int main(int argc, char **argv){
        unsigned char key[32] = {0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8, 0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b};
        unsigned char* msg = (unsigned char*)"Cryptographic Forum Research Group";
        int msglen = 34;
        unsigned char expected_output[16] = {0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6, 0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9};
        unsigned char out[16] = {0};
        poly1305_mac(out, msg, msglen, key);
        if (CRYPTO_memcmp(out, expected_output, 16) != 0) {
                printf("FAIL\n");
                printf("Got:\n\t");
                print16(out);
                printf("\nExpected:\n\t");
                print16(expected_output);
                printf("\n");
                return 1;
        } else {
                printf("PASS\n");
                return 0;
        }
}
