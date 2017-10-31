#include <assert.h>
#include <stdint.h>
#include <stdio.h>
typedef unsigned int uint128_t __attribute__((mode(TI)));

#define modulus_bytes 32
#define modulus_limbs 5
#define limb_t uint64_t

static const limb_t a24[modulus_limbs] = {121665};
static const limb_t limb_weight_gaps[modulus_limbs] = {51,51,51,51,51};

static void fe_add(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  out[0] = (x5 + x13);
  out[1] = (x7 + x15);
  out[2] = (x9 + x17);
  out[3] = (x11 + x19);
  out[4] = (x10 + x18);
  }}}}}}}}}}
}

static void fe_mul(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  { uint128_t x20 = ((uint128_t)x5 * x13);
  { uint128_t x21 = (((uint128_t)x5 * x15) + ((uint128_t)x7 * x13));
  { uint128_t x22 = ((((uint128_t)x5 * x17) + ((uint128_t)x9 * x13)) + ((uint128_t)x7 * x15));
  { uint128_t x23 = (((((uint128_t)x5 * x19) + ((uint128_t)x11 * x13)) + ((uint128_t)x7 * x17)) + ((uint128_t)x9 * x15));
  { uint128_t x24 = ((((((uint128_t)x5 * x18) + ((uint128_t)x10 * x13)) + ((uint128_t)x11 * x15)) + ((uint128_t)x7 * x19)) + ((uint128_t)x9 * x17));
  { uint64_t x25 = (x10 * 0x13);
  { uint64_t x26 = (x7 * 0x13);
  { uint64_t x27 = (x9 * 0x13);
  { uint64_t x28 = (x11 * 0x13);
  { uint128_t x29 = ((((x20 + ((uint128_t)x25 * x15)) + ((uint128_t)x26 * x18)) + ((uint128_t)x27 * x19)) + ((uint128_t)x28 * x17));
  { uint128_t x30 = (((x21 + ((uint128_t)x25 * x17)) + ((uint128_t)x27 * x18)) + ((uint128_t)x28 * x19));
  { uint128_t x31 = ((x22 + ((uint128_t)x25 * x19)) + ((uint128_t)x28 * x18));
  { uint128_t x32 = (x23 + ((uint128_t)x25 * x18));
  { uint64_t x33 = (uint64_t) (x29 >> 0x33);
  { uint64_t x34 = ((uint64_t)x29 & 0x7ffffffffffff);
  { uint128_t x35 = (x33 + x30);
  { uint64_t x36 = (uint64_t) (x35 >> 0x33);
  { uint64_t x37 = ((uint64_t)x35 & 0x7ffffffffffff);
  { uint128_t x38 = (x36 + x31);
  { uint64_t x39 = (uint64_t) (x38 >> 0x33);
  { uint64_t x40 = ((uint64_t)x38 & 0x7ffffffffffff);
  { uint128_t x41 = (x39 + x32);
  { uint64_t x42 = (uint64_t) (x41 >> 0x33);
  { uint64_t x43 = ((uint64_t)x41 & 0x7ffffffffffff);
  { uint128_t x44 = (x42 + x24);
  { uint64_t x45 = (uint64_t) (x44 >> 0x33);
  { uint64_t x46 = ((uint64_t)x44 & 0x7ffffffffffff);
  { uint64_t x47 = (x34 + (0x13 * x45));
  { uint64_t x48 = (x47 >> 0x33);
  { uint64_t x49 = (x47 & 0x7ffffffffffff);
  { uint64_t x50 = (x48 + x37);
  { uint64_t x51 = (x50 >> 0x33);
  { uint64_t x52 = (x50 & 0x7ffffffffffff);
  out[0] = x49;
  out[1] = x52;
  out[2] = (x51 + x40);
  out[3] = x43;
  out[4] = x46;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

static void fe_sqr(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x9 = (x2 * 0x2);
  { uint64_t x10 = (x4 * 0x2);
  { uint64_t x11 = ((x6 * 0x2) * 0x13);
  { uint64_t x12 = (x7 * 0x13);
  { uint64_t x13 = (x12 * 0x2);
  { uint128_t x14 = ((((uint128_t)x2 * x2) + ((uint128_t)x13 * x4)) + ((uint128_t)x11 * x8));
  { uint128_t x15 = ((((uint128_t)x9 * x4) + ((uint128_t)x13 * x6)) + ((uint128_t)x8 * (x8 * 0x13)));
  { uint128_t x16 = ((((uint128_t)x9 * x6) + ((uint128_t)x4 * x4)) + ((uint128_t)x13 * x8));
  { uint128_t x17 = ((((uint128_t)x9 * x8) + ((uint128_t)x10 * x6)) + ((uint128_t)x7 * x12));
  { uint128_t x18 = ((((uint128_t)x9 * x7) + ((uint128_t)x10 * x8)) + ((uint128_t)x6 * x6));
  { uint64_t x19 = (uint64_t) (x14 >> 0x33);
  { uint64_t x20 = ((uint64_t)x14 & 0x7ffffffffffff);
  { uint128_t x21 = (x19 + x15);
  { uint64_t x22 = (uint64_t) (x21 >> 0x33);
  { uint64_t x23 = ((uint64_t)x21 & 0x7ffffffffffff);
  { uint128_t x24 = (x22 + x16);
  { uint64_t x25 = (uint64_t) (x24 >> 0x33);
  { uint64_t x26 = ((uint64_t)x24 & 0x7ffffffffffff);
  { uint128_t x27 = (x25 + x17);
  { uint64_t x28 = (uint64_t) (x27 >> 0x33);
  { uint64_t x29 = ((uint64_t)x27 & 0x7ffffffffffff);
  { uint128_t x30 = (x28 + x18);
  { uint64_t x31 = (uint64_t) (x30 >> 0x33);
  { uint64_t x32 = ((uint64_t)x30 & 0x7ffffffffffff);
  { uint64_t x33 = (x20 + (0x13 * x31));
  { uint64_t x34 = (x33 >> 0x33);
  { uint64_t x35 = (x33 & 0x7ffffffffffff);
  { uint64_t x36 = (x34 + x23);
  { uint64_t x37 = (x36 >> 0x33);
  { uint64_t x38 = (x36 & 0x7ffffffffffff);
  out[0] = x35;
  out[1] = x38;
  out[2] = (x37 + x26);
  out[3] = x29;
  out[4] = x32;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}

static void fe_sub(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  out[0] = ((0xfffffffffffda + x5) - x13);
  out[1] = ((0xffffffffffffe + x7) - x15);
  out[2] = ((0xffffffffffffe + x9) - x17);
  out[3] = ((0xffffffffffffe + x11) - x19);
  out[4] = ((0xffffffffffffe + x10) - x18);
  }}}}}}}}}}
}


//========================================================================================================//

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
    printf("0x%016llx)<< %lu) + ", x[i], limb_weight_gaps[i-1]);
  }
  printf("0x%016llx", x[0]);
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

  {
    const uint8_t expected[32] = {0x89, 0x16, 0x1f, 0xde, 0x88, 0x7b, 0x2b, 0x53, 0xde, 0x54, 0x9a, 0xf4, 0x83, 0x94, 0x01, 0x06, 0xec, 0xc1, 0x14, 0xd6, 0x98, 0x2d, 0xaa, 0x98, 0x25, 0x6d, 0xe2, 0x3b, 0xdf, 0x77, 0x66, 0x1a};
    const uint8_t basepoint[32] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};


    uint8_t a[32] = {0}, b[32] = {0};
    uint8_t* in = a;
    uint8_t* out = b;
    a[0] = 1;

    for (int i = 0; i < 200; i++) {
      in[0] &= 248;
      in[31] &= 127;
      in[31] |= 64;

      crypto_scalarmult(out, in, 256, basepoint);
      uint8_t* t = out;
      out = in;
      in = t;
    }

    for (int i = 0; i < 32; i++) {
      if (in[i] != expected[i]) {
        return (i+1);
      }
    }
    return 0;
  }
}
