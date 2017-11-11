#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>

#define limb_t_(bitwidth) limb_t__(bitwidth)
#define PRIxlimb_(bitwidth) PRIxlimb__(bitwidth)
#define PRIulimb_(bitwidth) PRIulimb__(bitwidth)
#define limb_t__(bitwidth) uint ## bitwidth ## _t
#define PRIxlimb__(bitwidth) PRIx ## bitwidth
#define PRIulimb__(bitwidth) PRIu ## bitwidth

#ifndef modulus_bytes_val
#define modulus_bytes_val 32
#endif

#ifndef bitwidth
#define bitwidth 64
#endif

#ifndef a24_val
#define a24_val 121665
#endif

#ifndef modulus_limbs
#define modulus_limbs 5
#endif

#ifndef limb_weight_gaps_array
#define limb_weight_gaps_array {51,51,51,51,51}
#endif

#define modulus_bytes modulus_bytes_val

#define limb_t limb_t_(bitwidth)
#define PRIxlimb PRIxlimb_(bitwidth)
#define PRIulimb PRIulimb_(bitwidth)

static const limb_t a24[modulus_limbs] = {a24_val};
static const limb_t limb_weight_gaps[modulus_limbs] = limb_weight_gaps_array;

#if bitwidth >= 64
typedef unsigned int uint128_t __attribute__((mode(TI)));
#endif

// intrinsics?
#if 0

#include <immintrin.h>
#include <x86intrin.h>

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#else

static uint32_t _mulx_u32(uint32_t a, uint32_t b, uint32_t *high) {
  uint64_t x = (uint64_t)a * b;
  *high = (uint32_t) (x >> 32);
  return (uint32_t) x;
}

static uint32_t _addcarryx_u32(uint8_t c, uint32_t a, uint32_t b, uint32_t *low) {
  uint64_t x = (uint64_t)a + b + c;
  *low = (uint32_t) x;
  return (uint32_t) (x>>32);
}

static uint32_t _subborrow_u32(uint8_t c, uint32_t a, uint32_t b, uint32_t *low) {
  uint64_t t = ((uint64_t) b + c);
  uint64_t x = a-t;
  *low = (uint32_t) x;
  return (uint8_t) (x>>63);
}

static uint32_t cmovznz32(uint32_t t, uint32_t z, uint32_t nz) {
  t = -!!t;
  return (t&nz) | ((~t)&z);
}

#if bitwidth >= 64

static uint64_t _mulx_u64(uint64_t a, uint64_t b, uint64_t *high) {
  uint128_t x = (uint128_t)a * b;
  *high = (uint64_t) (x >> 64);
  return (uint64_t) x;
}

static uint64_t _addcarryx_u64(uint8_t c, uint64_t a, uint64_t b, uint64_t *low) {
  uint128_t x = (uint128_t)a + b + c;
  *low = (uint64_t) x;
  return (uint64_t) (x>>64);
}

static uint64_t _subborrow_u64(uint8_t c, uint64_t a, uint64_t b, uint64_t *low) {
  uint128_t t = ((uint128_t) b + c);
  uint128_t x = a-t;
  *low = (uint64_t) x;
  return (uint8_t) (x>>127);
}

static uint64_t cmovznz64(uint64_t t, uint64_t z, uint64_t nz) {
  t = -!!t;
  return (t&nz) | ((~t)&z);
}

#endif

#endif

static uint32_t _mulx_u32_out_u8(uint32_t a, uint32_t b, uint8_t *high) {
  uint32_t tmp_high;
  uint32_t ret = _mulx_u32(a, b, &tmp_high);
  *high = (uint8_t) (tmp_high);
  return ret;
}

# if bitwidth >= 64
static uint64_t _mulx_u64_out_u8(uint64_t a, uint64_t b, uint8_t *high) {
  uint64_t tmp_high;
  uint64_t ret = _mulx_u64(a, b, &tmp_high);
  *high = (uint8_t) (tmp_high);
  return ret;
}
#endif



#include "feadd.c"
#include "femul.c"
#include "fesquare.c"
#include "fesub.c"
#define fe_add feadd
#define fe_mul femul
#define fe_sqr fesquare
#define fe_sub fesub

static void fe_frombytes(limb_t x[modulus_limbs], const uint8_t s[modulus_bytes]) {
  limb_t byte_weight_gaps[modulus_bytes] = {0};
  for (int i = 0; i<modulus_bytes; i++) { byte_weight_gaps[i] = 8; }

  int modulus_bits = 0;
  for (int i = 0; i<modulus_limbs; i++) { modulus_bits += limb_weight_gaps[i]; }

  int i = 0;
  int in_limb = 0; int in_bit = 0;
  int out_limb = 0; int out_bit = 0;

  while (i < modulus_bits) {
    if (in_bit > byte_weight_gaps[in_limb]) {
      in_limb++;
      in_bit = 0;
    }
    if (out_bit > byte_weight_gaps[out_limb]) {
      out_limb++;
      out_bit = 0;
    }

    limb_t bit = (s[in_limb] >> in_bit)&1;
    x[out_limb] |= bit << out_bit;

    out_bit++; in_bit++; i++;
  }
}

static void fe_print(limb_t x[modulus_limbs]) {
  for (unsigned i=0; i<modulus_limbs-1; i++) { printf("(("); }
  for (unsigned i=modulus_limbs-1; i > 0; --i) {
    printf("0x%016"PRIxlimb")<< %"PRIulimb") + ", x[i], limb_weight_gaps[i-1]);
  }
  printf("0x%016"PRIxlimb, x[0]);
}

static void fe_cswap(limb_t bit, limb_t x[modulus_limbs], limb_t y[modulus_limbs]) {
  for (int i=0; i<modulus_limbs; ++i) { limb_t t = (x[i] ^ y[i])&(0-bit); x[i] ^= t; y[i] ^= t; }
}

static void crypto_scalarmult(uint8_t *out, const uint8_t *secret, size_t secretbits, const uint8_t *point) {
  limb_t a[modulus_limbs] = {0}; limb_t *nqpqx = a;
  limb_t b[modulus_limbs] = {1}; limb_t *nqpqz = b;
  limb_t c[modulus_limbs] ={1}; limb_t *nqx = c;
  limb_t d[modulus_limbs] = {0}; limb_t *nqz = d;
  limb_t e[modulus_limbs] = {0}; limb_t *nqpqx2 = e;
  limb_t f[modulus_limbs] = {1}; limb_t *nqpqz2 = f;
  limb_t g[modulus_limbs] = {0}; limb_t *nqx2 = g;
  limb_t h[modulus_limbs] = {1}; limb_t *nqz2 = h;
  limb_t *t;

  limb_t qmqp[modulus_limbs];
  fe_frombytes(qmqp, point);
  for (size_t i = 0; i<modulus_limbs; i++) { nqpqx[i] = qmqp[i]; }

  for (size_t i = secretbits-1; i < secretbits; --i) {
    limb_t bit = (secret[i/8] >> (i%8))&1;

    fe_cswap(bit, nqx, nqpqx);
    fe_cswap(bit, nqz, nqpqz);

    limb_t *x2 = nqx2;
    limb_t *z2 = nqz2;
    limb_t *x3 = nqpqx2;
    limb_t *z3 = nqpqz2;
    limb_t *x = nqx;
    limb_t *z = nqz;
    limb_t *xprime = nqpqx;
    limb_t *zprime = nqpqz;
    // fmonty(limb_t *x2, limb_t 0*z2, /* output 2Q */
    //        limb_t *x3, limb_t *z3, /* output Q + Q' */
    //        limb_t *x, limb_t *z,   /* input Q */
    //        limb_t *xprime, limb_t *zprime, /* input Q' */
    //        const limb_t *qmqp /* input Q - Q' */) {

    limb_t origx[modulus_limbs], origxprime[modulus_limbs], zzz[modulus_limbs], xx[modulus_limbs], zz[modulus_limbs], xxprime[modulus_limbs], zzprime[modulus_limbs], zzzprime[modulus_limbs];

    for (size_t i = 0; i<modulus_limbs; i++) { origx[i] = x[i]; }
    fe_add(x, x, z);
    fe_sub(z, origx, z);

    for (size_t i = 0; i<modulus_limbs; i++) { origxprime[i] = xprime[i]; }
    fe_add(xprime, xprime, zprime);
    fe_sub(zprime, origxprime, zprime);
    fe_mul(xxprime, xprime, z);
    fe_mul(zzprime, x, zprime);
    for (size_t i = 0; i<modulus_limbs; i++) { origxprime[i] = xxprime[i]; }
    fe_add(xxprime, xxprime, zzprime);
    fe_sub(zzprime, origxprime, zzprime);
    fe_sqr(x3, xxprime);
    fe_sqr(zzzprime, zzprime);
    fe_mul(z3, zzzprime, qmqp);

    fe_sqr(xx, x);
    fe_sqr(zz, z);
    fe_mul(x2, xx, zz);
    fe_sub(zz, xx, zz);
    fe_mul(zzz, zz, a24);
    fe_add(zzz, zzz, xx);
    fe_mul(z2, zz, zzz);

    // } fmonty

    fe_cswap(bit, nqx2, nqpqx2);
    fe_cswap(bit, nqz2, nqpqz2);

    t = nqx;
    nqx = nqx2;
    nqx2 = t;
    t = nqz;
    nqz = nqz2;
    nqz2 = t;
    t = nqpqx;
    nqpqx = nqpqx2;
    nqpqx2 = t;
    t = nqpqz;
    nqpqz = nqpqz2;
    nqpqz2 = t;

  }

  //TODO: implement inv, tobytes
  // fe_print(nqx); printf("\n");
  // fe_print(nqz); printf("\n");
  limb_t garble = 0;
  for (int i = 0; i < modulus_limbs; ++i) { garble ^= nqx[i] ^ nqz[i]; }
  for (int i = 0; i < modulus_bytes; ++i) { out[i] = garble&0xff; garble >>= 1; }
  // fe_inv(nqz, nqz);
  // fe_mul(nqx, nqx, nqz);
  // fe_tobytes
}


int main() {
  // {
  //   uint8_t out[modulus_bytes] = {0};
  //   uint8_t point[modulus_bytes] = {9};
  //   uint8_t secret[modulus_bytes] = {1};
  //   crypto_scalarmult(out, secret, 256, point);
  //   printf("0x"); for (int i = 31; i>=0; --i) { printf("%02x", out[i]); }; printf("\n");
  // }
  // return 0;

  //{
  //  const uint8_t expected[32] = {0x89, 0x16, 0x1f, 0xde, 0x88, 0x7b, 0x2b, 0x53, 0xde, 0x54, 0x9a, 0xf4, 0x83, 0x94, 0x01, 0x06, 0xec, 0xc1, 0x14, 0xd6, 0x98, 0x2d, 0xaa, 0x98, 0x25, 0x6d, 0xe2, 0x3b, 0xdf, 0x77, 0x66, 0x1a};
  //  const uint8_t basepoint[32] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};


  //  uint8_t a[32] = {0}, b[32] = {0};
  //  uint8_t* in = a;
  //  uint8_t* out = b;
  //  a[0] = 1;

  //  for (int i = 0; i < 200; i++) {
  //    in[0] &= 248;
  //    in[31] &= 127;
  //    in[31] |= 64;

  //    crypto_scalarmult(out, in, 256, basepoint);
  //    uint8_t* t = out;
  //    out = in;
  //    in = t;
  //  }

  //  for (int i = 0; i < 32; i++) {
  //    if (in[i] != expected[i]) {
  //      return (i+1);
  //    }
  //  }
  //  return 0;
  //}

  uint8_t secret[32];
  uint8_t point[modulus_bytes];

  for (int i = 0; i < modulus_bytes; i++) { point[modulus_bytes-i] = i; }

  for (int i = 0; i < 1000; i++) {
      for (int j = 0; j<modulus_bytes; j++) {
          secret[j%32] ^= point[j];
      }
      crypto_scalarmult(point, secret, 32*8, point);
  }
  __asm__ __volatile__("" :: "m" (point)); // do not optimize buf away
  return 0;
}
