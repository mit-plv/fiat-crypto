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


/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_to_bytes(uint8_t out1[17], const uint32_t arg1[5]) {
  poly1305_to_bytes((uintptr_t)out1, (uintptr_t)arg1);
}

/* NOTE: The following wrapper function is not covered by Coq proofs */
static void fiat_poly1305_from_bytes(uint32_t out1[5], const uint8_t arg1[17]) {
  poly1305_from_bytes((uintptr_t)out1, (uintptr_t)arg1);
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
