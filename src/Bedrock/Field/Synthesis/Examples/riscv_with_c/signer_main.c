#include <stdint.h>
#include <assert.h>
#include <string.h>

// this file is inlined from several files in the boringssl repository

static inline uint16_t CRYPTO_bswap2(uint16_t x) {
  return (x >> 8) | (x << 8);
}

static inline uint32_t CRYPTO_bswap4(uint32_t x) {
  x = (x >> 16) | (x << 16);
  x = ((x & 0xff00ff00) >> 8) | ((x & 0x00ff00ff) << 8);
  return x;
}

static inline uint64_t CRYPTO_bswap8(uint64_t x) {
  return CRYPTO_bswap4(x >> 32) | (((uint64_t)CRYPTO_bswap4(x)) << 32);
}

/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

// SHA-512.
typedef struct sha512_state_st SHA512_CTX;
// SHA512_CBLOCK is the block size of SHA-512.
#define SHA512_CBLOCK 128
// SHA512_DIGEST_LENGTH is the length of a SHA-512 digest.
#define SHA512_DIGEST_LENGTH 64
// SHA512_Init initialises |sha| and returns 1.
static int SHA512_Init(SHA512_CTX *sha);
// SHA512_Update adds |len| bytes from |data| to |sha| and returns 1.
static int SHA512_Update(SHA512_CTX *sha, const void *data, size_t len);
// SHA512_Final adds the final padding to |sha| and writes the resulting digest
// to |out|, which must have at least |SHA512_DIGEST_LENGTH| bytes of space. It
// returns one on success and zero on programmer error.
static int SHA512_Final(uint8_t out[SHA512_DIGEST_LENGTH],
                                SHA512_CTX *sha);
// SHA512 writes the digest of |len| bytes from |data| to |out| and returns
// |out|. There must be at least |SHA512_DIGEST_LENGTH| bytes of space in
// |out|.
static uint8_t *SHA512(const uint8_t *data, size_t len,
                               uint8_t out[SHA512_DIGEST_LENGTH]);
struct sha512_state_st {
  uint64_t h[8];
  uint64_t Nl, Nh;
  uint8_t p[128];
  unsigned num, md_len;
};


// The 32-bit hash algorithms share a common byte-order neutral collector and
// padding function implementations that operate on unaligned data,
// ../digest/md32_common.h. SHA-512 is the only 64-bit hash algorithm, as of
// this writing, so there is no need for a common collector/padding
// implementation yet.

static int SHA512_Init(SHA512_CTX *sha) {
  sha->h[0] = UINT64_C(0x6a09e667f3bcc908);
  sha->h[1] = UINT64_C(0xbb67ae8584caa73b);
  sha->h[2] = UINT64_C(0x3c6ef372fe94f82b);
  sha->h[3] = UINT64_C(0xa54ff53a5f1d36f1);
  sha->h[4] = UINT64_C(0x510e527fade682d1);
  sha->h[5] = UINT64_C(0x9b05688c2b3e6c1f);
  sha->h[6] = UINT64_C(0x1f83d9abfb41bd6b);
  sha->h[7] = UINT64_C(0x5be0cd19137e2179);

  sha->Nl = 0;
  sha->Nh = 0;
  sha->num = 0;
  sha->md_len = SHA512_DIGEST_LENGTH;
  return 1;
}

static uint8_t *SHA512(const uint8_t *data, size_t len,
                uint8_t out[SHA512_DIGEST_LENGTH]) {
  SHA512_CTX ctx;
  SHA512_Init(&ctx);
  SHA512_Update(&ctx, data, len);
  SHA512_Final(out, &ctx);
  // OPENSSL_cleanse(&ctx, sizeof(ctx));
  return out;
}

static void sha512_block_data_order(uint64_t *state, const uint8_t *in,
                                    size_t num_blocks);


static int SHA512_Update(SHA512_CTX *c, const void *in_data, size_t len) {
  uint64_t l;
  uint8_t *p = c->p;
  const uint8_t *data = in_data;

  if (len == 0) {
    return 1;
  }

  l = (c->Nl + (((uint64_t)len) << 3)) & UINT64_C(0xffffffffffffffff);
  if (l < c->Nl) {
    c->Nh++;
  }
  if (sizeof(len) >= 8) {
    c->Nh += (((uint64_t)len) >> 61);
  }
  c->Nl = l;

  if (c->num != 0) {
    size_t n = sizeof(c->p) - c->num;

    if (len < n) {
      memcpy(p + c->num, data, len);
      c->num += (unsigned int)len;
      return 1;
    } else {
      memcpy(p + c->num, data, n), c->num = 0;
      len -= n;
      data += n;
      sha512_block_data_order(c->h, p, 1);
    }
  }

  if (len >= sizeof(c->p)) {
    sha512_block_data_order(c->h, data, len / sizeof(c->p));
    data += len;
    len %= sizeof(c->p);
    data -= len;
  }

  if (len != 0) {
    memcpy(p, data, len);
    c->num = (int)len;
  }

  return 1;
}

static int SHA512_Final(uint8_t out[SHA512_DIGEST_LENGTH], SHA512_CTX *sha) {
  uint8_t *p = sha->p;
  size_t n = sha->num;

  p[n] = 0x80;  // There always is a room for one
  n++;
  if (n > (sizeof(sha->p) - 16)) {
    memset(p + n, 0, sizeof(sha->p) - n);
    n = 0;
    sha512_block_data_order(sha->h, p, 1);
  }

  memset(p + n, 0, sizeof(sha->p) - 16 - n);
  p[sizeof(sha->p) - 1] = (uint8_t)(sha->Nl);
  p[sizeof(sha->p) - 2] = (uint8_t)(sha->Nl >> 8);
  p[sizeof(sha->p) - 3] = (uint8_t)(sha->Nl >> 16);
  p[sizeof(sha->p) - 4] = (uint8_t)(sha->Nl >> 24);
  p[sizeof(sha->p) - 5] = (uint8_t)(sha->Nl >> 32);
  p[sizeof(sha->p) - 6] = (uint8_t)(sha->Nl >> 40);
  p[sizeof(sha->p) - 7] = (uint8_t)(sha->Nl >> 48);
  p[sizeof(sha->p) - 8] = (uint8_t)(sha->Nl >> 56);
  p[sizeof(sha->p) - 9] = (uint8_t)(sha->Nh);
  p[sizeof(sha->p) - 10] = (uint8_t)(sha->Nh >> 8);
  p[sizeof(sha->p) - 11] = (uint8_t)(sha->Nh >> 16);
  p[sizeof(sha->p) - 12] = (uint8_t)(sha->Nh >> 24);
  p[sizeof(sha->p) - 13] = (uint8_t)(sha->Nh >> 32);
  p[sizeof(sha->p) - 14] = (uint8_t)(sha->Nh >> 40);
  p[sizeof(sha->p) - 15] = (uint8_t)(sha->Nh >> 48);
  p[sizeof(sha->p) - 16] = (uint8_t)(sha->Nh >> 56);

  sha512_block_data_order(sha->h, p, 1);

  if (out == NULL) {
    // TODO(davidben): This NULL check is absent in other low-level hash 'final'
    // functions and is one of the few places one can fail.
    return 0;
  }

  assert(sha->md_len % 8 == 0);
  const size_t out_words = sha->md_len / 8;
  for (size_t i = 0; i < out_words; i++) {
    const uint64_t t = CRYPTO_bswap8(sha->h[i]);
    memcpy(out, &t, sizeof(t));
    out += sizeof(t);
  }

  return 1;
}

static const uint64_t K512[80] = {
    UINT64_C(0x428a2f98d728ae22), UINT64_C(0x7137449123ef65cd),
    UINT64_C(0xb5c0fbcfec4d3b2f), UINT64_C(0xe9b5dba58189dbbc),
    UINT64_C(0x3956c25bf348b538), UINT64_C(0x59f111f1b605d019),
    UINT64_C(0x923f82a4af194f9b), UINT64_C(0xab1c5ed5da6d8118),
    UINT64_C(0xd807aa98a3030242), UINT64_C(0x12835b0145706fbe),
    UINT64_C(0x243185be4ee4b28c), UINT64_C(0x550c7dc3d5ffb4e2),
    UINT64_C(0x72be5d74f27b896f), UINT64_C(0x80deb1fe3b1696b1),
    UINT64_C(0x9bdc06a725c71235), UINT64_C(0xc19bf174cf692694),
    UINT64_C(0xe49b69c19ef14ad2), UINT64_C(0xefbe4786384f25e3),
    UINT64_C(0x0fc19dc68b8cd5b5), UINT64_C(0x240ca1cc77ac9c65),
    UINT64_C(0x2de92c6f592b0275), UINT64_C(0x4a7484aa6ea6e483),
    UINT64_C(0x5cb0a9dcbd41fbd4), UINT64_C(0x76f988da831153b5),
    UINT64_C(0x983e5152ee66dfab), UINT64_C(0xa831c66d2db43210),
    UINT64_C(0xb00327c898fb213f), UINT64_C(0xbf597fc7beef0ee4),
    UINT64_C(0xc6e00bf33da88fc2), UINT64_C(0xd5a79147930aa725),
    UINT64_C(0x06ca6351e003826f), UINT64_C(0x142929670a0e6e70),
    UINT64_C(0x27b70a8546d22ffc), UINT64_C(0x2e1b21385c26c926),
    UINT64_C(0x4d2c6dfc5ac42aed), UINT64_C(0x53380d139d95b3df),
    UINT64_C(0x650a73548baf63de), UINT64_C(0x766a0abb3c77b2a8),
    UINT64_C(0x81c2c92e47edaee6), UINT64_C(0x92722c851482353b),
    UINT64_C(0xa2bfe8a14cf10364), UINT64_C(0xa81a664bbc423001),
    UINT64_C(0xc24b8b70d0f89791), UINT64_C(0xc76c51a30654be30),
    UINT64_C(0xd192e819d6ef5218), UINT64_C(0xd69906245565a910),
    UINT64_C(0xf40e35855771202a), UINT64_C(0x106aa07032bbd1b8),
    UINT64_C(0x19a4c116b8d2d0c8), UINT64_C(0x1e376c085141ab53),
    UINT64_C(0x2748774cdf8eeb99), UINT64_C(0x34b0bcb5e19b48a8),
    UINT64_C(0x391c0cb3c5c95a63), UINT64_C(0x4ed8aa4ae3418acb),
    UINT64_C(0x5b9cca4f7763e373), UINT64_C(0x682e6ff3d6b2b8a3),
    UINT64_C(0x748f82ee5defb2fc), UINT64_C(0x78a5636f43172f60),
    UINT64_C(0x84c87814a1f0ab72), UINT64_C(0x8cc702081a6439ec),
    UINT64_C(0x90befffa23631e28), UINT64_C(0xa4506cebde82bde9),
    UINT64_C(0xbef9a3f7b2c67915), UINT64_C(0xc67178f2e372532b),
    UINT64_C(0xca273eceea26619c), UINT64_C(0xd186b8c721c0c207),
    UINT64_C(0xeada7dd6cde0eb1e), UINT64_C(0xf57d4f7fee6ed178),
    UINT64_C(0x06f067aa72176fba), UINT64_C(0x0a637dc5a2c898a6),
    UINT64_C(0x113f9804bef90dae), UINT64_C(0x1b710b35131c471b),
    UINT64_C(0x28db77f523047d84), UINT64_C(0x32caab7b40c72493),
    UINT64_C(0x3c9ebe0a15c9bebc), UINT64_C(0x431d67c49c100d4c),
    UINT64_C(0x4cc5d4becb3e42b6), UINT64_C(0x597f299cfc657e2a),
    UINT64_C(0x5fcb6fab3ad6faec), UINT64_C(0x6c44198c4a475817),
};

static inline uint64_t load_u64_be(const void *ptr) {
  uint64_t ret;
  memcpy(&ret, ptr, sizeof(ret));
  return CRYPTO_bswap8(ret);
}

#define ROTR(x, s) (((x) >> s) | (x) << (64 - s))
#define Sigma0(x) (ROTR((x), 28) ^ ROTR((x), 34) ^ ROTR((x), 39))
#define Sigma1(x) (ROTR((x), 14) ^ ROTR((x), 18) ^ ROTR((x), 41))
#define sigma0(x) (ROTR((x), 1) ^ ROTR((x), 8) ^ ((x) >> 7))
#define sigma1(x) (ROTR((x), 19) ^ ROTR((x), 61) ^ ((x) >> 6))

#define Ch(x, y, z) (((x) & (y)) ^ ((~(x)) & (z)))
#define Maj(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

#define ROUND_00_15(i, a, b, c, d, e, f, g, h)   \
  do {                                           \
    T1 += h + Sigma1(e) + Ch(e, f, g) + K512[i]; \
    h = Sigma0(a) + Maj(a, b, c);                \
    d += T1;                                     \
    h += T1;                                     \
  } while (0)

#define ROUND_16_80(i, j, a, b, c, d, e, f, g, h, X)   \
  do {                                                 \
    s0 = X[(j + 1) & 0x0f];                            \
    s0 = sigma0(s0);                                   \
    s1 = X[(j + 14) & 0x0f];                           \
    s1 = sigma1(s1);                                   \
    T1 = X[(j) & 0x0f] += s0 + s1 + X[(j + 9) & 0x0f]; \
    ROUND_00_15(i + j, a, b, c, d, e, f, g, h);        \
  } while (0)

static void sha512_block_data_order(uint64_t *state, const uint8_t *in,
                                    size_t num) {
  uint64_t a, b, c, d, e, f, g, h, s0, s1, T1;
  uint64_t X[16];
  int i;

  while (num--) {

    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    f = state[5];
    g = state[6];
    h = state[7];

    T1 = X[0] = load_u64_be(in);
    ROUND_00_15(0, a, b, c, d, e, f, g, h);
    T1 = X[1] = load_u64_be(in + 8);
    ROUND_00_15(1, h, a, b, c, d, e, f, g);
    T1 = X[2] = load_u64_be(in + 2 * 8);
    ROUND_00_15(2, g, h, a, b, c, d, e, f);
    T1 = X[3] = load_u64_be(in + 3 * 8);
    ROUND_00_15(3, f, g, h, a, b, c, d, e);
    T1 = X[4] = load_u64_be(in + 4 * 8);
    ROUND_00_15(4, e, f, g, h, a, b, c, d);
    T1 = X[5] = load_u64_be(in + 5 * 8);
    ROUND_00_15(5, d, e, f, g, h, a, b, c);
    T1 = X[6] = load_u64_be(in + 6 * 8);
    ROUND_00_15(6, c, d, e, f, g, h, a, b);
    T1 = X[7] = load_u64_be(in + 7 * 8);
    ROUND_00_15(7, b, c, d, e, f, g, h, a);
    T1 = X[8] = load_u64_be(in + 8 * 8);
    ROUND_00_15(8, a, b, c, d, e, f, g, h);
    T1 = X[9] = load_u64_be(in + 9 * 8);
    ROUND_00_15(9, h, a, b, c, d, e, f, g);
    T1 = X[10] = load_u64_be(in + 10 * 8);
    ROUND_00_15(10, g, h, a, b, c, d, e, f);
    T1 = X[11] = load_u64_be(in + 11 * 8);
    ROUND_00_15(11, f, g, h, a, b, c, d, e);
    T1 = X[12] = load_u64_be(in + 12 * 8);
    ROUND_00_15(12, e, f, g, h, a, b, c, d);
    T1 = X[13] = load_u64_be(in + 13 * 8);
    ROUND_00_15(13, d, e, f, g, h, a, b, c);
    T1 = X[14] = load_u64_be(in + 14 * 8);
    ROUND_00_15(14, c, d, e, f, g, h, a, b);
    T1 = X[15] = load_u64_be(in + 15 * 8);
    ROUND_00_15(15, b, c, d, e, f, g, h, a);

    for (i = 16; i < 80; i += 16) {
      ROUND_16_80(i, 0, a, b, c, d, e, f, g, h, X);
      ROUND_16_80(i, 1, h, a, b, c, d, e, f, g, X);
      ROUND_16_80(i, 2, g, h, a, b, c, d, e, f, X);
      ROUND_16_80(i, 3, f, g, h, a, b, c, d, e, X);
      ROUND_16_80(i, 4, e, f, g, h, a, b, c, d, X);
      ROUND_16_80(i, 5, d, e, f, g, h, a, b, c, X);
      ROUND_16_80(i, 6, c, d, e, f, g, h, a, b, X);
      ROUND_16_80(i, 7, b, c, d, e, f, g, h, a, X);
      ROUND_16_80(i, 8, a, b, c, d, e, f, g, h, X);
      ROUND_16_80(i, 9, h, a, b, c, d, e, f, g, X);
      ROUND_16_80(i, 10, g, h, a, b, c, d, e, f, X);
      ROUND_16_80(i, 11, f, g, h, a, b, c, d, e, X);
      ROUND_16_80(i, 12, e, f, g, h, a, b, c, d, X);
      ROUND_16_80(i, 13, d, e, f, g, h, a, b, c, X);
      ROUND_16_80(i, 14, c, d, e, f, g, h, a, b, X);
      ROUND_16_80(i, 15, b, c, d, e, f, g, h, a, X);
    }

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;

    in += 16 * 8;
  }
}

#undef ROTR
#undef Sigma0
#undef Sigma1
#undef sigma0
#undef sigma1
#undef Ch
#undef Maj
#undef ROUND_00_15
#undef ROUND_16_80

/*
The MIT License (MIT)
Copyright (c) 2015-2016 the fiat-crypto authors (see
https://github.com/mit-plv/fiat-crypto/blob/master/AUTHORS).
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

// Some of this code is taken from the ref10 version of Ed25519 in SUPERCOP
// 20141124 (http://bench.cr.yp.to/supercop.html). That code is released as
// public domain. Other parts have been replaced to call into code generated by
// Fiat (https://github.com/mit-plv/fiat-crypto) in //third_party/fiat.


static inline uint32_t value_barrier_u32(uint32_t a) {
#if !defined(OPENSSL_NO_ASM) && (defined(__GNUC__) || defined(__clang__))
  __asm__("" : "+r"(a) : /* no inputs */);
#endif
  return a;
}

typedef unsigned char fiat_25519_uint1;
typedef signed char fiat_25519_int1;
#if (-1 & 3) != 3
#error "This code only works on a two's complement system"
#endif
/*
 * The function fiat_25519_addcarryx_u26 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^26
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^26⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x3ffffff]
 *   arg3: [0x0 ~> 0x3ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x3ffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_25519_addcarryx_u26(uint32_t* out1, fiat_25519_uint1* out2, fiat_25519_uint1 arg1, uint32_t arg2, uint32_t arg3) {
  uint32_t x1 = ((arg1 + arg2) + arg3);
  uint32_t x2 = (x1 & UINT32_C(0x3ffffff));
  fiat_25519_uint1 x3 = (fiat_25519_uint1)(x1 >> 26);
  *out1 = x2;
  *out2 = x3;
}
/*
 * The function fiat_25519_subborrowx_u26 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^26
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^26⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x3ffffff]
 *   arg3: [0x0 ~> 0x3ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x3ffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_25519_subborrowx_u26(uint32_t* out1, fiat_25519_uint1* out2, fiat_25519_uint1 arg1, uint32_t arg2, uint32_t arg3) {
  int32_t x1 = ((int32_t)(arg2 - arg1) - (int32_t)arg3);
  fiat_25519_int1 x2 = (fiat_25519_int1)(x1 >> 26);
  uint32_t x3 = (x1 & UINT32_C(0x3ffffff));
  *out1 = x3;
  *out2 = (fiat_25519_uint1)(0x0 - x2);
}
/*
 * The function fiat_25519_addcarryx_u25 is an addition with carry.
 * Postconditions:
 *   out1 = (arg1 + arg2 + arg3) mod 2^25
 *   out2 = ⌊(arg1 + arg2 + arg3) / 2^25⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x1ffffff]
 *   arg3: [0x0 ~> 0x1ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x1ffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_25519_addcarryx_u25(uint32_t* out1, fiat_25519_uint1* out2, fiat_25519_uint1 arg1, uint32_t arg2, uint32_t arg3) {
  uint32_t x1 = ((arg1 + arg2) + arg3);
  uint32_t x2 = (x1 & UINT32_C(0x1ffffff));
  fiat_25519_uint1 x3 = (fiat_25519_uint1)(x1 >> 25);
  *out1 = x2;
  *out2 = x3;
}
/*
 * The function fiat_25519_subborrowx_u25 is a subtraction with borrow.
 * Postconditions:
 *   out1 = (-arg1 + arg2 + -arg3) mod 2^25
 *   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^25⌋
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0x1ffffff]
 *   arg3: [0x0 ~> 0x1ffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0x1ffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_25519_subborrowx_u25(uint32_t* out1, fiat_25519_uint1* out2, fiat_25519_uint1 arg1, uint32_t arg2, uint32_t arg3) {
  int32_t x1 = ((int32_t)(arg2 - arg1) - (int32_t)arg3);
  fiat_25519_int1 x2 = (fiat_25519_int1)(x1 >> 25);
  uint32_t x3 = (x1 & UINT32_C(0x1ffffff));
  *out1 = x3;
  *out2 = (fiat_25519_uint1)(0x0 - x2);
}
/*
 * The function fiat_25519_cmovznz_u32 is a single-word conditional move.
 * Postconditions:
 *   out1 = (if arg1 = 0 then arg2 else arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffff]
 *   arg3: [0x0 ~> 0xffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffff]
 */
static void fiat_25519_cmovznz_u32(uint32_t* out1, fiat_25519_uint1 arg1, uint32_t arg2, uint32_t arg3) {
  fiat_25519_uint1 x1 = (!(!arg1));
  uint32_t x2 = ((fiat_25519_int1)(0x0 - x1) & UINT32_C(0xffffffff));
  // Note this line has been patched from the synthesized code to add value
  // barriers.
  //
  // Clang recognizes this pattern as a select. While it usually transforms it
  // to a cmov, it sometimes further transforms it into a branch, which we do
  // not want.
  uint32_t x3 = ((value_barrier_u32(x2) & arg3) | (value_barrier_u32(~x2) & arg2));
  *out1 = x3;
}

/*
 * The function fiat_25519_carry_mul multiplies two field elements and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 *   arg2: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 */
static void fiat_25519_carry_mul(uint32_t out1[10], const uint32_t arg1[10], const uint32_t arg2[10]) {
  //curve25519_carry_mul(out1, arg1, arg2);//segfaults
  uint64_t x1 = ((uint64_t)(arg1[9]) * ((arg2[9]) * UINT8_C(0x26)));
  uint64_t x2 = ((uint64_t)(arg1[9]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x3 = ((uint64_t)(arg1[9]) * ((arg2[7]) * UINT8_C(0x26)));
  uint64_t x4 = ((uint64_t)(arg1[9]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x5 = ((uint64_t)(arg1[9]) * ((arg2[5]) * UINT8_C(0x26)));
  uint64_t x6 = ((uint64_t)(arg1[9]) * ((arg2[4]) * UINT8_C(0x13)));
  uint64_t x7 = ((uint64_t)(arg1[9]) * ((arg2[3]) * UINT8_C(0x26)));
  uint64_t x8 = ((uint64_t)(arg1[9]) * ((arg2[2]) * UINT8_C(0x13)));
  uint64_t x9 = ((uint64_t)(arg1[9]) * ((arg2[1]) * UINT8_C(0x26)));
  uint64_t x10 = ((uint64_t)(arg1[8]) * ((arg2[9]) * UINT8_C(0x13)));
  uint64_t x11 = ((uint64_t)(arg1[8]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x12 = ((uint64_t)(arg1[8]) * ((arg2[7]) * UINT8_C(0x13)));
  uint64_t x13 = ((uint64_t)(arg1[8]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x14 = ((uint64_t)(arg1[8]) * ((arg2[5]) * UINT8_C(0x13)));
  uint64_t x15 = ((uint64_t)(arg1[8]) * ((arg2[4]) * UINT8_C(0x13)));
  uint64_t x16 = ((uint64_t)(arg1[8]) * ((arg2[3]) * UINT8_C(0x13)));
  uint64_t x17 = ((uint64_t)(arg1[8]) * ((arg2[2]) * UINT8_C(0x13)));
  uint64_t x18 = ((uint64_t)(arg1[7]) * ((arg2[9]) * UINT8_C(0x26)));
  uint64_t x19 = ((uint64_t)(arg1[7]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x20 = ((uint64_t)(arg1[7]) * ((arg2[7]) * UINT8_C(0x26)));
  uint64_t x21 = ((uint64_t)(arg1[7]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x22 = ((uint64_t)(arg1[7]) * ((arg2[5]) * UINT8_C(0x26)));
  uint64_t x23 = ((uint64_t)(arg1[7]) * ((arg2[4]) * UINT8_C(0x13)));
  uint64_t x24 = ((uint64_t)(arg1[7]) * ((arg2[3]) * UINT8_C(0x26)));
  uint64_t x25 = ((uint64_t)(arg1[6]) * ((arg2[9]) * UINT8_C(0x13)));
  uint64_t x26 = ((uint64_t)(arg1[6]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x27 = ((uint64_t)(arg1[6]) * ((arg2[7]) * UINT8_C(0x13)));
  uint64_t x28 = ((uint64_t)(arg1[6]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x29 = ((uint64_t)(arg1[6]) * ((arg2[5]) * UINT8_C(0x13)));
  uint64_t x30 = ((uint64_t)(arg1[6]) * ((arg2[4]) * UINT8_C(0x13)));
  uint64_t x31 = ((uint64_t)(arg1[5]) * ((arg2[9]) * UINT8_C(0x26)));
  uint64_t x32 = ((uint64_t)(arg1[5]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x33 = ((uint64_t)(arg1[5]) * ((arg2[7]) * UINT8_C(0x26)));
  uint64_t x34 = ((uint64_t)(arg1[5]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x35 = ((uint64_t)(arg1[5]) * ((arg2[5]) * UINT8_C(0x26)));
  uint64_t x36 = ((uint64_t)(arg1[4]) * ((arg2[9]) * UINT8_C(0x13)));
  uint64_t x37 = ((uint64_t)(arg1[4]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x38 = ((uint64_t)(arg1[4]) * ((arg2[7]) * UINT8_C(0x13)));
  uint64_t x39 = ((uint64_t)(arg1[4]) * ((arg2[6]) * UINT8_C(0x13)));
  uint64_t x40 = ((uint64_t)(arg1[3]) * ((arg2[9]) * UINT8_C(0x26)));
  uint64_t x41 = ((uint64_t)(arg1[3]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x42 = ((uint64_t)(arg1[3]) * ((arg2[7]) * UINT8_C(0x26)));
  uint64_t x43 = ((uint64_t)(arg1[2]) * ((arg2[9]) * UINT8_C(0x13)));
  uint64_t x44 = ((uint64_t)(arg1[2]) * ((arg2[8]) * UINT8_C(0x13)));
  uint64_t x45 = ((uint64_t)(arg1[1]) * ((arg2[9]) * UINT8_C(0x26)));
  uint64_t x46 = ((uint64_t)(arg1[9]) * (arg2[0]));
  uint64_t x47 = ((uint64_t)(arg1[8]) * (arg2[1]));
  uint64_t x48 = ((uint64_t)(arg1[8]) * (arg2[0]));
  uint64_t x49 = ((uint64_t)(arg1[7]) * (arg2[2]));
  uint64_t x50 = ((uint64_t)(arg1[7]) * ((arg2[1]) * 0x2));
  uint64_t x51 = ((uint64_t)(arg1[7]) * (arg2[0]));
  uint64_t x52 = ((uint64_t)(arg1[6]) * (arg2[3]));
  uint64_t x53 = ((uint64_t)(arg1[6]) * (arg2[2]));
  uint64_t x54 = ((uint64_t)(arg1[6]) * (arg2[1]));
  uint64_t x55 = ((uint64_t)(arg1[6]) * (arg2[0]));
  uint64_t x56 = ((uint64_t)(arg1[5]) * (arg2[4]));
  uint64_t x57 = ((uint64_t)(arg1[5]) * ((arg2[3]) * 0x2));
  uint64_t x58 = ((uint64_t)(arg1[5]) * (arg2[2]));
  uint64_t x59 = ((uint64_t)(arg1[5]) * ((arg2[1]) * 0x2));
  uint64_t x60 = ((uint64_t)(arg1[5]) * (arg2[0]));
  uint64_t x61 = ((uint64_t)(arg1[4]) * (arg2[5]));
  uint64_t x62 = ((uint64_t)(arg1[4]) * (arg2[4]));
  uint64_t x63 = ((uint64_t)(arg1[4]) * (arg2[3]));
  uint64_t x64 = ((uint64_t)(arg1[4]) * (arg2[2]));
  uint64_t x65 = ((uint64_t)(arg1[4]) * (arg2[1]));
  uint64_t x66 = ((uint64_t)(arg1[4]) * (arg2[0]));
  uint64_t x67 = ((uint64_t)(arg1[3]) * (arg2[6]));
  uint64_t x68 = ((uint64_t)(arg1[3]) * ((arg2[5]) * 0x2));
  uint64_t x69 = ((uint64_t)(arg1[3]) * (arg2[4]));
  uint64_t x70 = ((uint64_t)(arg1[3]) * ((arg2[3]) * 0x2));
  uint64_t x71 = ((uint64_t)(arg1[3]) * (arg2[2]));
  uint64_t x72 = ((uint64_t)(arg1[3]) * ((arg2[1]) * 0x2));
  uint64_t x73 = ((uint64_t)(arg1[3]) * (arg2[0]));
  uint64_t x74 = ((uint64_t)(arg1[2]) * (arg2[7]));
  uint64_t x75 = ((uint64_t)(arg1[2]) * (arg2[6]));
  uint64_t x76 = ((uint64_t)(arg1[2]) * (arg2[5]));
  uint64_t x77 = ((uint64_t)(arg1[2]) * (arg2[4]));
  uint64_t x78 = ((uint64_t)(arg1[2]) * (arg2[3]));
  uint64_t x79 = ((uint64_t)(arg1[2]) * (arg2[2]));
  uint64_t x80 = ((uint64_t)(arg1[2]) * (arg2[1]));
  uint64_t x81 = ((uint64_t)(arg1[2]) * (arg2[0]));
  uint64_t x82 = ((uint64_t)(arg1[1]) * (arg2[8]));
  uint64_t x83 = ((uint64_t)(arg1[1]) * ((arg2[7]) * 0x2));
  uint64_t x84 = ((uint64_t)(arg1[1]) * (arg2[6]));
  uint64_t x85 = ((uint64_t)(arg1[1]) * ((arg2[5]) * 0x2));
  uint64_t x86 = ((uint64_t)(arg1[1]) * (arg2[4]));
  uint64_t x87 = ((uint64_t)(arg1[1]) * ((arg2[3]) * 0x2));
  uint64_t x88 = ((uint64_t)(arg1[1]) * (arg2[2]));
  uint64_t x89 = ((uint64_t)(arg1[1]) * ((arg2[1]) * 0x2));
  uint64_t x90 = ((uint64_t)(arg1[1]) * (arg2[0]));
  uint64_t x91 = ((uint64_t)(arg1[0]) * (arg2[9]));
  uint64_t x92 = ((uint64_t)(arg1[0]) * (arg2[8]));
  uint64_t x93 = ((uint64_t)(arg1[0]) * (arg2[7]));
  uint64_t x94 = ((uint64_t)(arg1[0]) * (arg2[6]));
  uint64_t x95 = ((uint64_t)(arg1[0]) * (arg2[5]));
  uint64_t x96 = ((uint64_t)(arg1[0]) * (arg2[4]));
  uint64_t x97 = ((uint64_t)(arg1[0]) * (arg2[3]));
  uint64_t x98 = ((uint64_t)(arg1[0]) * (arg2[2]));
  uint64_t x99 = ((uint64_t)(arg1[0]) * (arg2[1]));
  uint64_t x100 = ((uint64_t)(arg1[0]) * (arg2[0]));
  uint64_t x101 = (x100 + (x45 + (x44 + (x42 + (x39 + (x35 + (x30 + (x24 + (x17 + x9)))))))));
  uint64_t x102 = (x101 >> 26);
  uint32_t x103 = (uint32_t)(x101 & UINT32_C(0x3ffffff));
  uint64_t x104 = (x91 + (x82 + (x74 + (x67 + (x61 + (x56 + (x52 + (x49 + (x47 + x46)))))))));
  uint64_t x105 = (x92 + (x83 + (x75 + (x68 + (x62 + (x57 + (x53 + (x50 + (x48 + x1)))))))));
  uint64_t x106 = (x93 + (x84 + (x76 + (x69 + (x63 + (x58 + (x54 + (x51 + (x10 + x2)))))))));
  uint64_t x107 = (x94 + (x85 + (x77 + (x70 + (x64 + (x59 + (x55 + (x18 + (x11 + x3)))))))));
  uint64_t x108 = (x95 + (x86 + (x78 + (x71 + (x65 + (x60 + (x25 + (x19 + (x12 + x4)))))))));
  uint64_t x109 = (x96 + (x87 + (x79 + (x72 + (x66 + (x31 + (x26 + (x20 + (x13 + x5)))))))));
  uint64_t x110 = (x97 + (x88 + (x80 + (x73 + (x36 + (x32 + (x27 + (x21 + (x14 + x6)))))))));
  uint64_t x111 = (x98 + (x89 + (x81 + (x40 + (x37 + (x33 + (x28 + (x22 + (x15 + x7)))))))));
  uint64_t x112 = (x99 + (x90 + (x43 + (x41 + (x38 + (x34 + (x29 + (x23 + (x16 + x8)))))))));
  uint64_t x113 = (x102 + x112);
  uint64_t x114 = (x113 >> 25);
  uint32_t x115 = (uint32_t)(x113 & UINT32_C(0x1ffffff));
  uint64_t x116 = (x114 + x111);
  uint64_t x117 = (x116 >> 26);
  uint32_t x118 = (uint32_t)(x116 & UINT32_C(0x3ffffff));
  uint64_t x119 = (x117 + x110);
  uint64_t x120 = (x119 >> 25);
  uint32_t x121 = (uint32_t)(x119 & UINT32_C(0x1ffffff));
  uint64_t x122 = (x120 + x109);
  uint64_t x123 = (x122 >> 26);
  uint32_t x124 = (uint32_t)(x122 & UINT32_C(0x3ffffff));
  uint64_t x125 = (x123 + x108);
  uint64_t x126 = (x125 >> 25);
  uint32_t x127 = (uint32_t)(x125 & UINT32_C(0x1ffffff));
  uint64_t x128 = (x126 + x107);
  uint64_t x129 = (x128 >> 26);
  uint32_t x130 = (uint32_t)(x128 & UINT32_C(0x3ffffff));
  uint64_t x131 = (x129 + x106);
  uint64_t x132 = (x131 >> 25);
  uint32_t x133 = (uint32_t)(x131 & UINT32_C(0x1ffffff));
  uint64_t x134 = (x132 + x105);
  uint64_t x135 = (x134 >> 26);
  uint32_t x136 = (uint32_t)(x134 & UINT32_C(0x3ffffff));
  uint64_t x137 = (x135 + x104);
  uint64_t x138 = (x137 >> 25);
  uint32_t x139 = (uint32_t)(x137 & UINT32_C(0x1ffffff));
  uint64_t x140 = (x138 * UINT8_C(0x13));
  uint64_t x141 = (x103 + x140);
  uint32_t x142 = (uint32_t)(x141 >> 26);
  uint32_t x143 = (uint32_t)(x141 & UINT32_C(0x3ffffff));
  uint32_t x144 = (x142 + x115);
  fiat_25519_uint1 x145 = (fiat_25519_uint1)(x144 >> 25);
  uint32_t x146 = (x144 & UINT32_C(0x1ffffff));
  uint32_t x147 = (x145 + x118);
  out1[0] = x143;
  out1[1] = x146;
  out1[2] = x147;
  out1[3] = x121;
  out1[4] = x124;
  out1[5] = x127;
  out1[6] = x130;
  out1[7] = x133;
  out1[8] = x136;
  out1[9] = x139;
}

/*
 * The function fiat_25519_carry_square squares a field element and reduces the result.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 * eval arg1) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 */
static void fiat_25519_carry_square(uint32_t out1[10], const uint32_t arg1[10]) {
  curve25519_carry_square(out1, arg1);
}

/*
 * The function fiat_25519_carry reduces a field element.
 * Postconditions:
 *   eval out1 mod m = eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 */
static void fiat_25519_carry(uint32_t out1[10], const uint32_t arg1[10]) {
  curve25519_carry(out1, arg1);
}
/*
 * The function fiat_25519_add adds two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 + eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 *   arg2: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 */
static void fiat_25519_add(uint32_t out1[10], const uint32_t arg1[10], const uint32_t arg2[10]) {
  uint32_t x1 = ((arg1[0]) + (arg2[0]));
  uint32_t x2 = ((arg1[1]) + (arg2[1]));
  uint32_t x3 = ((arg1[2]) + (arg2[2]));
  uint32_t x4 = ((arg1[3]) + (arg2[3]));
  uint32_t x5 = ((arg1[4]) + (arg2[4]));
  uint32_t x6 = ((arg1[5]) + (arg2[5]));
  uint32_t x7 = ((arg1[6]) + (arg2[6]));
  uint32_t x8 = ((arg1[7]) + (arg2[7]));
  uint32_t x9 = ((arg1[8]) + (arg2[8]));
  uint32_t x10 = ((arg1[9]) + (arg2[9]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
  out1[5] = x6;
  out1[6] = x7;
  out1[7] = x8;
  out1[8] = x9;
  out1[9] = x10;
}
/*
 * The function fiat_25519_sub subtracts two field elements.
 * Postconditions:
 *   eval out1 mod m = (eval arg1 - eval arg2) mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 *   arg2: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999], [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
 */
static void fiat_25519_sub(uint32_t out1[10], const uint32_t arg1[10], const uint32_t arg2[10]) {
  uint32_t x1 = ((UINT32_C(0x7ffffda) + (arg1[0])) - (arg2[0]));
  uint32_t x2 = ((UINT32_C(0x3fffffe) + (arg1[1])) - (arg2[1]));
  uint32_t x3 = ((UINT32_C(0x7fffffe) + (arg1[2])) - (arg2[2]));
  uint32_t x4 = ((UINT32_C(0x3fffffe) + (arg1[3])) - (arg2[3]));
  uint32_t x5 = ((UINT32_C(0x7fffffe) + (arg1[4])) - (arg2[4]));
  uint32_t x6 = ((UINT32_C(0x3fffffe) + (arg1[5])) - (arg2[5]));
  uint32_t x7 = ((UINT32_C(0x7fffffe) + (arg1[6])) - (arg2[6]));
  uint32_t x8 = ((UINT32_C(0x3fffffe) + (arg1[7])) - (arg2[7]));
  uint32_t x9 = ((UINT32_C(0x7fffffe) + (arg1[8])) - (arg2[8]));
  uint32_t x10 = ((UINT32_C(0x3fffffe) + (arg1[9])) - (arg2[9]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
  out1[5] = x6;
  out1[6] = x7;
  out1[7] = x8;
  out1[8] = x9;
  out1[9] = x10;
}
/*
 * The function fiat_25519_selectznz is a multi-limb conditional select.
 * Postconditions:
 *   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
 *
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 *   arg3: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
 */
static void fiat_25519_selectznz(uint32_t out1[10], fiat_25519_uint1 arg1, const uint32_t arg2[10], const uint32_t arg3[10]) {
  uint32_t x1;
  fiat_25519_cmovznz_u32(&x1, arg1, (arg2[0]), (arg3[0]));
  uint32_t x2;
  fiat_25519_cmovznz_u32(&x2, arg1, (arg2[1]), (arg3[1]));
  uint32_t x3;
  fiat_25519_cmovznz_u32(&x3, arg1, (arg2[2]), (arg3[2]));
  uint32_t x4;
  fiat_25519_cmovznz_u32(&x4, arg1, (arg2[3]), (arg3[3]));
  uint32_t x5;
  fiat_25519_cmovznz_u32(&x5, arg1, (arg2[4]), (arg3[4]));
  uint32_t x6;
  fiat_25519_cmovznz_u32(&x6, arg1, (arg2[5]), (arg3[5]));
  uint32_t x7;
  fiat_25519_cmovznz_u32(&x7, arg1, (arg2[6]), (arg3[6]));
  uint32_t x8;
  fiat_25519_cmovznz_u32(&x8, arg1, (arg2[7]), (arg3[7]));
  uint32_t x9;
  fiat_25519_cmovznz_u32(&x9, arg1, (arg2[8]), (arg3[8]));
  uint32_t x10;
  fiat_25519_cmovznz_u32(&x10, arg1, (arg2[9]), (arg3[9]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
  out1[3] = x4;
  out1[4] = x5;
  out1[5] = x6;
  out1[6] = x7;
  out1[7] = x8;
  out1[8] = x9;
  out1[9] = x10;
}
/*
 * The function fiat_25519_to_bytes serializes a field element to bytes in little-endian order.
 * Postconditions:
 *   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..31]
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
 */
static void fiat_25519_to_bytes(uint8_t out1[32], const uint32_t arg1[10]) {
  uint32_t x1;
  fiat_25519_uint1 x2;
  fiat_25519_subborrowx_u26(&x1, &x2, 0x0, (arg1[0]), UINT32_C(0x3ffffed));
  uint32_t x3;
  fiat_25519_uint1 x4;
  fiat_25519_subborrowx_u25(&x3, &x4, x2, (arg1[1]), UINT32_C(0x1ffffff));
  uint32_t x5;
  fiat_25519_uint1 x6;
  fiat_25519_subborrowx_u26(&x5, &x6, x4, (arg1[2]), UINT32_C(0x3ffffff));
  uint32_t x7;
  fiat_25519_uint1 x8;
  fiat_25519_subborrowx_u25(&x7, &x8, x6, (arg1[3]), UINT32_C(0x1ffffff));
  uint32_t x9;
  fiat_25519_uint1 x10;
  fiat_25519_subborrowx_u26(&x9, &x10, x8, (arg1[4]), UINT32_C(0x3ffffff));
  uint32_t x11;
  fiat_25519_uint1 x12;
  fiat_25519_subborrowx_u25(&x11, &x12, x10, (arg1[5]), UINT32_C(0x1ffffff));
  uint32_t x13;
  fiat_25519_uint1 x14;
  fiat_25519_subborrowx_u26(&x13, &x14, x12, (arg1[6]), UINT32_C(0x3ffffff));
  uint32_t x15;
  fiat_25519_uint1 x16;
  fiat_25519_subborrowx_u25(&x15, &x16, x14, (arg1[7]), UINT32_C(0x1ffffff));
  uint32_t x17;
  fiat_25519_uint1 x18;
  fiat_25519_subborrowx_u26(&x17, &x18, x16, (arg1[8]), UINT32_C(0x3ffffff));
  uint32_t x19;
  fiat_25519_uint1 x20;
  fiat_25519_subborrowx_u25(&x19, &x20, x18, (arg1[9]), UINT32_C(0x1ffffff));
  uint32_t x21;
  fiat_25519_cmovznz_u32(&x21, x20, 0x0, UINT32_C(0xffffffff));
  uint32_t x22;
  fiat_25519_uint1 x23;
  fiat_25519_addcarryx_u26(&x22, &x23, 0x0, x1, (x21 & UINT32_C(0x3ffffed)));
  uint32_t x24;
  fiat_25519_uint1 x25;
  fiat_25519_addcarryx_u25(&x24, &x25, x23, x3, (x21 & UINT32_C(0x1ffffff)));
  uint32_t x26;
  fiat_25519_uint1 x27;
  fiat_25519_addcarryx_u26(&x26, &x27, x25, x5, (x21 & UINT32_C(0x3ffffff)));
  uint32_t x28;
  fiat_25519_uint1 x29;
  fiat_25519_addcarryx_u25(&x28, &x29, x27, x7, (x21 & UINT32_C(0x1ffffff)));
  uint32_t x30;
  fiat_25519_uint1 x31;
  fiat_25519_addcarryx_u26(&x30, &x31, x29, x9, (x21 & UINT32_C(0x3ffffff)));
  uint32_t x32;
  fiat_25519_uint1 x33;
  fiat_25519_addcarryx_u25(&x32, &x33, x31, x11, (x21 & UINT32_C(0x1ffffff)));
  uint32_t x34;
  fiat_25519_uint1 x35;
  fiat_25519_addcarryx_u26(&x34, &x35, x33, x13, (x21 & UINT32_C(0x3ffffff)));
  uint32_t x36;
  fiat_25519_uint1 x37;
  fiat_25519_addcarryx_u25(&x36, &x37, x35, x15, (x21 & UINT32_C(0x1ffffff)));
  uint32_t x38;
  fiat_25519_uint1 x39;
  fiat_25519_addcarryx_u26(&x38, &x39, x37, x17, (x21 & UINT32_C(0x3ffffff)));
  uint32_t x40;
  fiat_25519_uint1 x41;
  fiat_25519_addcarryx_u25(&x40, &x41, x39, x19, (x21 & UINT32_C(0x1ffffff)));
  uint32_t x42 = (x40 << 6);
  uint32_t x43 = (x38 << 4);
  uint32_t x44 = (x36 << 3);
  uint32_t x45 = (x34 * (uint32_t)0x2);
  uint32_t x46 = (x30 << 6);
  uint32_t x47 = (x28 << 5);
  uint32_t x48 = (x26 << 3);
  uint32_t x49 = (x24 << 2);
  uint32_t x50 = (x22 >> 8);
  uint8_t x51 = (uint8_t)(x22 & UINT8_C(0xff));
  uint32_t x52 = (x50 >> 8);
  uint8_t x53 = (uint8_t)(x50 & UINT8_C(0xff));
  uint8_t x54 = (uint8_t)(x52 >> 8);
  uint8_t x55 = (uint8_t)(x52 & UINT8_C(0xff));
  uint32_t x56 = (x54 + x49);
  uint32_t x57 = (x56 >> 8);
  uint8_t x58 = (uint8_t)(x56 & UINT8_C(0xff));
  uint32_t x59 = (x57 >> 8);
  uint8_t x60 = (uint8_t)(x57 & UINT8_C(0xff));
  uint8_t x61 = (uint8_t)(x59 >> 8);
  uint8_t x62 = (uint8_t)(x59 & UINT8_C(0xff));
  uint32_t x63 = (x61 + x48);
  uint32_t x64 = (x63 >> 8);
  uint8_t x65 = (uint8_t)(x63 & UINT8_C(0xff));
  uint32_t x66 = (x64 >> 8);
  uint8_t x67 = (uint8_t)(x64 & UINT8_C(0xff));
  uint8_t x68 = (uint8_t)(x66 >> 8);
  uint8_t x69 = (uint8_t)(x66 & UINT8_C(0xff));
  uint32_t x70 = (x68 + x47);
  uint32_t x71 = (x70 >> 8);
  uint8_t x72 = (uint8_t)(x70 & UINT8_C(0xff));
  uint32_t x73 = (x71 >> 8);
  uint8_t x74 = (uint8_t)(x71 & UINT8_C(0xff));
  uint8_t x75 = (uint8_t)(x73 >> 8);
  uint8_t x76 = (uint8_t)(x73 & UINT8_C(0xff));
  uint32_t x77 = (x75 + x46);
  uint32_t x78 = (x77 >> 8);
  uint8_t x79 = (uint8_t)(x77 & UINT8_C(0xff));
  uint32_t x80 = (x78 >> 8);
  uint8_t x81 = (uint8_t)(x78 & UINT8_C(0xff));
  uint8_t x82 = (uint8_t)(x80 >> 8);
  uint8_t x83 = (uint8_t)(x80 & UINT8_C(0xff));
  uint8_t x84 = (uint8_t)(x82 & UINT8_C(0xff));
  uint32_t x85 = (x32 >> 8);
  uint8_t x86 = (uint8_t)(x32 & UINT8_C(0xff));
  uint32_t x87 = (x85 >> 8);
  uint8_t x88 = (uint8_t)(x85 & UINT8_C(0xff));
  fiat_25519_uint1 x89 = (fiat_25519_uint1)(x87 >> 8);
  uint8_t x90 = (uint8_t)(x87 & UINT8_C(0xff));
  uint32_t x91 = (x89 + x45);
  uint32_t x92 = (x91 >> 8);
  uint8_t x93 = (uint8_t)(x91 & UINT8_C(0xff));
  uint32_t x94 = (x92 >> 8);
  uint8_t x95 = (uint8_t)(x92 & UINT8_C(0xff));
  uint8_t x96 = (uint8_t)(x94 >> 8);
  uint8_t x97 = (uint8_t)(x94 & UINT8_C(0xff));
  uint32_t x98 = (x96 + x44);
  uint32_t x99 = (x98 >> 8);
  uint8_t x100 = (uint8_t)(x98 & UINT8_C(0xff));
  uint32_t x101 = (x99 >> 8);
  uint8_t x102 = (uint8_t)(x99 & UINT8_C(0xff));
  uint8_t x103 = (uint8_t)(x101 >> 8);
  uint8_t x104 = (uint8_t)(x101 & UINT8_C(0xff));
  uint32_t x105 = (x103 + x43);
  uint32_t x106 = (x105 >> 8);
  uint8_t x107 = (uint8_t)(x105 & UINT8_C(0xff));
  uint32_t x108 = (x106 >> 8);
  uint8_t x109 = (uint8_t)(x106 & UINT8_C(0xff));
  uint8_t x110 = (uint8_t)(x108 >> 8);
  uint8_t x111 = (uint8_t)(x108 & UINT8_C(0xff));
  uint32_t x112 = (x110 + x42);
  uint32_t x113 = (x112 >> 8);
  uint8_t x114 = (uint8_t)(x112 & UINT8_C(0xff));
  uint32_t x115 = (x113 >> 8);
  uint8_t x116 = (uint8_t)(x113 & UINT8_C(0xff));
  uint8_t x117 = (uint8_t)(x115 >> 8);
  uint8_t x118 = (uint8_t)(x115 & UINT8_C(0xff));
  out1[0] = x51;
  out1[1] = x53;
  out1[2] = x55;
  out1[3] = x58;
  out1[4] = x60;
  out1[5] = x62;
  out1[6] = x65;
  out1[7] = x67;
  out1[8] = x69;
  out1[9] = x72;
  out1[10] = x74;
  out1[11] = x76;
  out1[12] = x79;
  out1[13] = x81;
  out1[14] = x83;
  out1[15] = x84;
  out1[16] = x86;
  out1[17] = x88;
  out1[18] = x90;
  out1[19] = x93;
  out1[20] = x95;
  out1[21] = x97;
  out1[22] = x100;
  out1[23] = x102;
  out1[24] = x104;
  out1[25] = x107;
  out1[26] = x109;
  out1[27] = x111;
  out1[28] = x114;
  out1[29] = x116;
  out1[30] = x118;
  out1[31] = x117;
}
/*
 * The function fiat_25519_from_bytes deserializes a field element from bytes in little-endian order.
 * Postconditions:
 *   eval out1 mod m = bytes_eval arg1 mod m
 *
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333], [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
 */
static void fiat_25519_from_bytes(uint32_t out1[10], const uint8_t arg1[32]) {
  uint32_t x1 = ((uint32_t)(arg1[31]) << 18);
  uint32_t x2 = ((uint32_t)(arg1[30]) << 10);
  uint32_t x3 = ((uint32_t)(arg1[29]) << 2);
  uint32_t x4 = ((uint32_t)(arg1[28]) << 20);
  uint32_t x5 = ((uint32_t)(arg1[27]) << 12);
  uint32_t x6 = ((uint32_t)(arg1[26]) << 4);
  uint32_t x7 = ((uint32_t)(arg1[25]) << 21);
  uint32_t x8 = ((uint32_t)(arg1[24]) << 13);
  uint32_t x9 = ((uint32_t)(arg1[23]) << 5);
  uint32_t x10 = ((uint32_t)(arg1[22]) << 23);
  uint32_t x11 = ((uint32_t)(arg1[21]) << 15);
  uint32_t x12 = ((uint32_t)(arg1[20]) << 7);
  uint32_t x13 = ((uint32_t)(arg1[19]) << 24);
  uint32_t x14 = ((uint32_t)(arg1[18]) << 16);
  uint32_t x15 = ((uint32_t)(arg1[17]) << 8);
  uint8_t x16 = (arg1[16]);
  uint32_t x17 = ((uint32_t)(arg1[15]) << 18);
  uint32_t x18 = ((uint32_t)(arg1[14]) << 10);
  uint32_t x19 = ((uint32_t)(arg1[13]) << 2);
  uint32_t x20 = ((uint32_t)(arg1[12]) << 19);
  uint32_t x21 = ((uint32_t)(arg1[11]) << 11);
  uint32_t x22 = ((uint32_t)(arg1[10]) << 3);
  uint32_t x23 = ((uint32_t)(arg1[9]) << 21);
  uint32_t x24 = ((uint32_t)(arg1[8]) << 13);
  uint32_t x25 = ((uint32_t)(arg1[7]) << 5);
  uint32_t x26 = ((uint32_t)(arg1[6]) << 22);
  uint32_t x27 = ((uint32_t)(arg1[5]) << 14);
  uint32_t x28 = ((uint32_t)(arg1[4]) << 6);
  uint32_t x29 = ((uint32_t)(arg1[3]) << 24);
  uint32_t x30 = ((uint32_t)(arg1[2]) << 16);
  uint32_t x31 = ((uint32_t)(arg1[1]) << 8);
  uint8_t x32 = (arg1[0]);
  uint32_t x33 = (x32 + (x31 + (x30 + x29)));
  uint8_t x34 = (uint8_t)(x33 >> 26);
  uint32_t x35 = (x33 & UINT32_C(0x3ffffff));
  uint32_t x36 = (x3 + (x2 + x1));
  uint32_t x37 = (x6 + (x5 + x4));
  uint32_t x38 = (x9 + (x8 + x7));
  uint32_t x39 = (x12 + (x11 + x10));
  uint32_t x40 = (x16 + (x15 + (x14 + x13)));
  uint32_t x41 = (x19 + (x18 + x17));
  uint32_t x42 = (x22 + (x21 + x20));
  uint32_t x43 = (x25 + (x24 + x23));
  uint32_t x44 = (x28 + (x27 + x26));
  uint32_t x45 = (x34 + x44);
  uint8_t x46 = (uint8_t)(x45 >> 25);
  uint32_t x47 = (x45 & UINT32_C(0x1ffffff));
  uint32_t x48 = (x46 + x43);
  uint8_t x49 = (uint8_t)(x48 >> 26);
  uint32_t x50 = (x48 & UINT32_C(0x3ffffff));
  uint32_t x51 = (x49 + x42);
  uint8_t x52 = (uint8_t)(x51 >> 25);
  uint32_t x53 = (x51 & UINT32_C(0x1ffffff));
  uint32_t x54 = (x52 + x41);
  uint32_t x55 = (x54 & UINT32_C(0x3ffffff));
  uint8_t x56 = (uint8_t)(x40 >> 25);
  uint32_t x57 = (x40 & UINT32_C(0x1ffffff));
  uint32_t x58 = (x56 + x39);
  uint8_t x59 = (uint8_t)(x58 >> 26);
  uint32_t x60 = (x58 & UINT32_C(0x3ffffff));
  uint32_t x61 = (x59 + x38);
  uint8_t x62 = (uint8_t)(x61 >> 25);
  uint32_t x63 = (x61 & UINT32_C(0x1ffffff));
  uint32_t x64 = (x62 + x37);
  uint8_t x65 = (uint8_t)(x64 >> 26);
  uint32_t x66 = (x64 & UINT32_C(0x3ffffff));
  uint32_t x67 = (x65 + x36);
  out1[0] = x35;
  out1[1] = x47;
  out1[2] = x50;
  out1[3] = x53;
  out1[4] = x55;
  out1[5] = x57;
  out1[6] = x60;
  out1[7] = x63;
  out1[8] = x66;
  out1[9] = x67;
}

/* Copyright (c) 2020, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */


#define ED25519_PRIVATE_KEY_LEN 64
#define ED25519_PUBLIC_KEY_LEN 32
#define ED25519_SIGNATURE_LEN 64
// fe means field element. Here the field is \Z/(2^255-19). An element t,
// entries t[0]...t[9], represents the integer t[0]+2^26 t[1]+2^51 t[2]+2^77
// t[3]+2^102 t[4]+...+2^230 t[9].
// fe limbs are bounded by 1.125*2^26,1.125*2^25,1.125*2^26,1.125*2^25,etc.
// Multiplication and carrying produce fe from fe_loose.
typedef struct fe { uint32_t v[10]; } fe;
// fe_loose limbs are bounded by 3.375*2^26,3.375*2^25,3.375*2^26,3.375*2^25,etc.
// Addition and subtraction produce fe_loose from (fe, fe).
typedef struct fe_loose { uint32_t v[10]; } fe_loose;

// ge means group element.
//
// Here the group is the set of pairs (x,y) of field elements (see fe.h)
// satisfying -x^2 + y^2 = 1 + d x^2y^2
// where d = -121665/121666.
//
// Representations:
//   ge_p2 (projective): (X:Y:Z) satisfying x=X/Z, y=Y/Z
//   ge_p3 (extended): (X:Y:Z:T) satisfying x=X/Z, y=Y/Z, XY=ZT
//   ge_p1p1 (completed): ((X:Z),(Y:T)) satisfying x=X/Z, y=Y/T
//   ge_precomp (Duif): (y+x,y-x,2dxy)
typedef struct {
  fe X;
  fe Y;
  fe Z;
} ge_p2;
typedef struct {
  fe X;
  fe Y;
  fe Z;
  fe T;
} ge_p3;
typedef struct {
  fe_loose X;
  fe_loose Y;
  fe_loose Z;
  fe_loose T;
} ge_p1p1;
typedef struct {
  fe_loose yplusx;
  fe_loose yminusx;
  fe_loose xy2d;
} ge_precomp;
typedef struct {
  fe_loose YplusX;
  fe_loose YminusX;
  fe_loose Z;
  fe_loose T2d;
} ge_cached;
static void x25519_ge_p3_to_cached(ge_cached *r, const ge_p3 *p);
static void x25519_ge_p1p1_to_p3(ge_p3 *r, const ge_p1p1 *p);
static void x25519_ge_add(ge_p1p1 *r, const ge_p3 *p, const ge_cached *q);
static void x25519_ge_scalarmult_small_precomp(
    ge_p3 *h, const uint8_t a[32], const uint8_t precomp_table[15 * 2 * 32]);
static void x25519_ge_scalarmult_base(ge_p3 *h, const uint8_t a[32]);
static void x25519_sc_reduce(uint8_t s[64]);


// The field functions are shared by Ed25519 and X25519 where possible.
// These constants generated from make_curve25519_tables.py
static const fe d = {{
    56195235, 13857412, 51736253, 6949390, 114729, 24766616, 60832955, 30306712,
    48412415, 21499315
}};
static const fe sqrtm1 = {{
    34513072, 25610706, 9377949, 3500415, 12389472, 33281959, 41962654,
    31548777, 326685, 11406482
}};
static const fe d2 = {{
    45281625, 27714825, 36363642, 13898781, 229458, 15978800, 54557047,
    27058993, 29715967, 9444199
}};

static const uint8_t precomp_generator[2 * 32] = {
    0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95,
    0x60, 0xc7, 0x2c, 0x69, 0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0,
    0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21, 0x58, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66};

// Low-level intrinsic operations
static uint64_t load_3(const uint8_t *in) {
  uint64_t result;
  result = (uint64_t)in[0];
  result |= ((uint64_t)in[1]) << 8;
  result |= ((uint64_t)in[2]) << 16;
  return result;
}
static uint64_t load_4(const uint8_t *in) {
  uint64_t result;
  result = (uint64_t)in[0];
  result |= ((uint64_t)in[1]) << 8;
  result |= ((uint64_t)in[2]) << 16;
  result |= ((uint64_t)in[3]) << 24;
  return result;
}
//
// Field operations.
typedef uint32_t fe_limb_t;
#define FE_NUM_LIMBS 10
// assert_fe asserts that |f| satisfies bounds:
//
//  [[0x0 ~> 0x4666666], [0x0 ~> 0x2333333],
//   [0x0 ~> 0x4666666], [0x0 ~> 0x2333333],
//   [0x0 ~> 0x4666666], [0x0 ~> 0x2333333],
//   [0x0 ~> 0x4666666], [0x0 ~> 0x2333333],
//   [0x0 ~> 0x4666666], [0x0 ~> 0x2333333]]
//
// See comments in curve25519_32.h for which functions use these bounds for
// inputs or outputs.
#define assert_fe(f)                                                     \
  do {                                                                   \
    for (unsigned _assert_fe_i = 0; _assert_fe_i < 10; _assert_fe_i++) { \
      assert(f[_assert_fe_i] <=                                          \
             ((_assert_fe_i & 1) ? 0x2333333u : 0x4666666u));            \
    }                                                                    \
  } while (0)
// assert_fe_loose asserts that |f| satisfies bounds:
//
//  [[0x0 ~> 0xd333332], [0x0 ~> 0x6999999],
//   [0x0 ~> 0xd333332], [0x0 ~> 0x6999999],
//   [0x0 ~> 0xd333332], [0x0 ~> 0x6999999],
//   [0x0 ~> 0xd333332], [0x0 ~> 0x6999999],
//   [0x0 ~> 0xd333332], [0x0 ~> 0x6999999]]
//
// See comments in curve25519_32.h for which functions use these bounds for
// inputs or outputs.
#define assert_fe_loose(f)                                               \
  do {                                                                   \
    for (unsigned _assert_fe_i = 0; _assert_fe_i < 10; _assert_fe_i++) { \
      assert(f[_assert_fe_i] <=                                          \
             ((_assert_fe_i & 1) ? 0x6999999u : 0xd333332u));            \
    }                                                                    \
  } while (0)


// OPENSSL_STATIC_ASSERT(sizeof(fe) == sizeof(fe_limb_t) * FE_NUM_LIMBS, "fe_limb_t[FE_NUM_LIMBS] is inconsistent with fe");

static void fe_frombytes_strict(fe *h, const uint8_t s[32]) {
  // |fiat_25519_from_bytes| requires the top-most bit be clear.
  assert((s[31] & 0x80) == 0);
  fiat_25519_from_bytes(h->v, s);
  assert_fe(h->v);
}
static void fe_tobytes(uint8_t s[32], const fe *f) {
  assert_fe(f->v);
  fiat_25519_to_bytes(s, f->v);
}
// h = 0
static void fe_0(fe *h) {
  memset(h, 0, sizeof(fe));
}
static void fe_loose_0(fe_loose *h) {
  memset(h, 0, sizeof(fe_loose));
}
// h = 1
static void fe_1(fe *h) {
  memset(h, 0, sizeof(fe));
  h->v[0] = 1;
}
static void fe_loose_1(fe_loose *h) {
  memset(h, 0, sizeof(fe_loose));
  h->v[0] = 1;
}
// h = f + g
// Can overlap h with f or g.
static void fe_add(fe_loose *h, const fe *f, const fe *g) {
  assert_fe(f->v);
  assert_fe(g->v);
  fiat_25519_add(h->v, f->v, g->v);
  assert_fe_loose(h->v);
}
// h = f - g
// Can overlap h with f or g.
static void fe_sub(fe_loose *h, const fe *f, const fe *g) {
  assert_fe(f->v);
  assert_fe(g->v);
  fiat_25519_sub(h->v, f->v, g->v);
  assert_fe_loose(h->v);
}
static void fe_carry(fe *h, const fe_loose* f) {
  assert_fe_loose(f->v);
  fiat_25519_carry(h->v, f->v);
  assert_fe(h->v);
}
static void fe_mul_impl(fe_limb_t out[FE_NUM_LIMBS],
                        const fe_limb_t in1[FE_NUM_LIMBS],
                        const fe_limb_t in2[FE_NUM_LIMBS]) {
  assert_fe_loose(in1);
  assert_fe_loose(in2);
  fiat_25519_carry_mul(out, in1, in2);
  assert_fe(out);
}
static void fe_mul_ltt(fe_loose *h, const fe *f, const fe *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_mul_llt(fe_loose *h, const fe_loose *f, const fe *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_mul_ttt(fe *h, const fe *f, const fe *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_mul_tlt(fe *h, const fe_loose *f, const fe *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_mul_ttl(fe *h, const fe *f, const fe_loose *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_mul_tll(fe *h, const fe_loose *f, const fe_loose *g) {
  fe_mul_impl(h->v, f->v, g->v);
}
static void fe_sq_tl(fe *h, const fe_loose *f) {
  assert_fe_loose(f->v);
  fiat_25519_carry_square(h->v, f->v);
  assert_fe(h->v);
}
static void fe_sq_tt(fe *h, const fe *f) {
  assert_fe_loose(f->v);
  fiat_25519_carry_square(h->v, f->v);
  assert_fe(h->v);
}
// Replace (f,g) with (g,g) if b == 1;
// replace (f,g) with (f,g) if b == 0.
//
// Preconditions: b in {0,1}.
static void fe_cmov(fe_loose *f, const fe_loose *g, fe_limb_t b) {
  // Silence an unused function warning. |fiat_25519_selectznz| isn't quite the
  // calling convention the rest of this code wants, so implement it by hand.
  (void)fiat_25519_selectznz;
  b = 0-b;
  for (unsigned i = 0; i < FE_NUM_LIMBS; i++) {
    fe_limb_t x = f->v[i] ^ g->v[i];
    x &= b;
    f->v[i] ^= x;
  }
}
static void fe_copy_lt(fe_loose *h, const fe *f) {
  // OPENSSL_STATIC_ASSERT(sizeof(fe_loose) == sizeof(fe), "fe and fe_loose mismatch");
  memmove(h, f, sizeof(fe));
}
static void fe_loose_invert(fe *out, const fe_loose *z) {
  fe t0;
  fe t1;
  fe t2;
  fe t3;
  int i;
  fe_sq_tl(&t0, z);
  fe_sq_tt(&t1, &t0);
  for (i = 1; i < 2; ++i) {
    fe_sq_tt(&t1, &t1);
  }
  fe_mul_tlt(&t1, z, &t1);
  fe_mul_ttt(&t0, &t0, &t1);
  fe_sq_tt(&t2, &t0);
  fe_mul_ttt(&t1, &t1, &t2);
  fe_sq_tt(&t2, &t1);
  for (i = 1; i < 5; ++i) {
    fe_sq_tt(&t2, &t2);
  }
  fe_mul_ttt(&t1, &t2, &t1);
  fe_sq_tt(&t2, &t1);
  for (i = 1; i < 10; ++i) {
    fe_sq_tt(&t2, &t2);
  }
  fe_mul_ttt(&t2, &t2, &t1);
  fe_sq_tt(&t3, &t2);
  for (i = 1; i < 20; ++i) {
    fe_sq_tt(&t3, &t3);
  }
  fe_mul_ttt(&t2, &t3, &t2);
  fe_sq_tt(&t2, &t2);
  for (i = 1; i < 10; ++i) {
    fe_sq_tt(&t2, &t2);
  }
  fe_mul_ttt(&t1, &t2, &t1);
  fe_sq_tt(&t2, &t1);
  for (i = 1; i < 50; ++i) {
    fe_sq_tt(&t2, &t2);
  }
  fe_mul_ttt(&t2, &t2, &t1);
  fe_sq_tt(&t3, &t2);
  for (i = 1; i < 100; ++i) {
    fe_sq_tt(&t3, &t3);
  }
  fe_mul_ttt(&t2, &t3, &t2);
  fe_sq_tt(&t2, &t2);
  for (i = 1; i < 50; ++i) {
    fe_sq_tt(&t2, &t2);
  }
  fe_mul_ttt(&t1, &t2, &t1);
  fe_sq_tt(&t1, &t1);
  for (i = 1; i < 5; ++i) {
    fe_sq_tt(&t1, &t1);
  }
  fe_mul_ttt(out, &t1, &t0);
}
static void fe_invert(fe *out, const fe *z) {
  fe_loose l;
  fe_copy_lt(&l, z);
  fe_loose_invert(out, &l);
}
// return 1 if f is in {1,3,5,...,q-2}
// return 0 if f is in {0,2,4,...,q-1}
static int fe_isnegative(const fe *f) {
  uint8_t s[32];
  fe_tobytes(s, f);
  return s[0] & 1;
}
// Group operations.
static void ge_p3_tobytes(uint8_t s[32], const ge_p3 *h) {
  fe recip;
  fe x;
  fe y;
  fe_invert(&recip, &h->Z);
  fe_mul_ttt(&x, &h->X, &recip);
  fe_mul_ttt(&y, &h->Y, &recip);
  fe_tobytes(s, &y);
  s[31] ^= fe_isnegative(&x) << 7;
}
static void ge_p3_0(ge_p3 *h) {
  fe_0(&h->X);
  fe_1(&h->Y);
  fe_1(&h->Z);
  fe_0(&h->T);
}
static void ge_precomp_0(ge_precomp *h) {
  fe_loose_1(&h->yplusx);
  fe_loose_1(&h->yminusx);
  fe_loose_0(&h->xy2d);
}
// r = p
static void x25519_ge_p3_to_cached(ge_cached *r, const ge_p3 *p) {
  fe_add(&r->YplusX, &p->Y, &p->X);
  fe_sub(&r->YminusX, &p->Y, &p->X);
  fe_copy_lt(&r->Z, &p->Z);
  fe_mul_ltt(&r->T2d, &p->T, &d2);
}
// r = p
static void x25519_ge_p1p1_to_p3(ge_p3 *r, const ge_p1p1 *p) {
  fe_mul_tll(&r->X, &p->X, &p->T);
  fe_mul_tll(&r->Y, &p->Y, &p->Z);
  fe_mul_tll(&r->Z, &p->Z, &p->T);
  fe_mul_tll(&r->T, &p->X, &p->Y);
}
// r = p + q
static void ge_madd(ge_p1p1 *r, const ge_p3 *p, const ge_precomp *q) {
  fe trY, trZ, trT;
  fe_add(&r->X, &p->Y, &p->X);
  fe_sub(&r->Y, &p->Y, &p->X);
  fe_mul_tll(&trZ, &r->X, &q->yplusx);
  fe_mul_tll(&trY, &r->Y, &q->yminusx);
  fe_mul_tlt(&trT, &q->xy2d, &p->T);
  fe_add(&r->T, &p->Z, &p->Z);
  fe_sub(&r->X, &trZ, &trY);
  fe_add(&r->Y, &trZ, &trY);
  fe_carry(&trZ, &r->T);
  fe_add(&r->Z, &trZ, &trT);
  fe_sub(&r->T, &trZ, &trT);
}
// r = p + q
static void x25519_ge_add(ge_p1p1 *r, const ge_p3 *p, const ge_cached *q) {
  fe trX, trY, trZ, trT;
  fe_add(&r->X, &p->Y, &p->X);
  fe_sub(&r->Y, &p->Y, &p->X);
  fe_mul_tll(&trZ, &r->X, &q->YplusX);
  fe_mul_tll(&trY, &r->Y, &q->YminusX);
  fe_mul_tlt(&trT, &q->T2d, &p->T);
  fe_mul_ttl(&trX, &p->Z, &q->Z);
  fe_add(&r->T, &trX, &trX);
  fe_sub(&r->X, &trZ, &trY);
  fe_add(&r->Y, &trZ, &trY);
  fe_carry(&trZ, &r->T);
  fe_add(&r->Z, &trZ, &trT);
  fe_sub(&r->T, &trZ, &trT);
}
static uint8_t equal(signed char b, signed char c) {
  uint8_t ub = b;
  uint8_t uc = c;
  uint8_t x = ub ^ uc;  // 0: yes; 1..255: no
  uint32_t y = x;       // 0: yes; 1..255: no
  y -= 1;               // 4294967295: yes; 0..254: no
  y >>= 31;             // 1: yes; 0: no
  return y;
}
static void cmov(ge_precomp *t, const ge_precomp *u, uint8_t b) {
  fe_cmov(&t->yplusx, &u->yplusx, b);
  fe_cmov(&t->yminusx, &u->yminusx, b);
  fe_cmov(&t->xy2d, &u->xy2d, b);
}
static void x25519_ge_scalarmult_small_precomp(
    ge_p3 *h, const uint8_t a[32], const uint8_t precomp_table[15 * 2 * 32]) {
  ge_precomp generator;
  { // deserialize the generator
    const uint8_t *bytes = &precomp_table[0];
    fe x, y;
    fe_frombytes_strict(&x, bytes);
    fe_frombytes_strict(&y, bytes + 32);
    fe_add(&generator.yplusx, &y, &x);
    fe_sub(&generator.yminusx, &y, &x);
    fe_mul_ltt(&generator.xy2d, &x, &y);
    fe_mul_llt(&generator.xy2d, &generator.xy2d, &d2);
  }
  ge_p3_0(h);
  for (unsigned i = 255; i < 256; i--) {
    ge_precomp e;
    ge_precomp_0(&e);
    cmov(&e, &generator, 1&(a[i/8]>>(i&7)));

    { // h = 2h // XYZT += XYZT
      ge_cached cached;
      x25519_ge_p3_to_cached(&cached, h);
      ge_p1p1 r;
      x25519_ge_add(&r, h, &cached);
      x25519_ge_p1p1_to_p3(h, &r);
    }
    { // h += e // XYZT += precomputed
      ge_p1p1 r;
      ge_madd(&r, h, &e);
      x25519_ge_p1p1_to_p3(h, &r);
    }
  }
}
static void x25519_ge_scalarmult_base(ge_p3 *h, const uint8_t a[32]) {
  x25519_ge_scalarmult_small_precomp(h, a, precomp_generator);
}
// int64_lshift21 returns |a << 21| but is defined when shifting bits into the
// sign bit. This works around a language flaw in C.
static inline int64_t int64_lshift21(int64_t a) {
  return (int64_t)((uint64_t)a << 21);
}
// The set of scalars is \Z/l
// where l = 2^252 + 27742317777372353535851937790883648493.
// Input:
//   s[0]+256*s[1]+...+256^63*s[63] = s
//
// Output:
//   s[0]+256*s[1]+...+256^31*s[31] = s mod l
//   where l = 2^252 + 27742317777372353535851937790883648493.
//   Overwrites s in place.
static void x25519_sc_reduce(uint8_t s[64]) {
  int64_t s0 = 2097151 & load_3(s);
  int64_t s1 = 2097151 & (load_4(s + 2) >> 5);
  int64_t s2 = 2097151 & (load_3(s + 5) >> 2);
  int64_t s3 = 2097151 & (load_4(s + 7) >> 7);
  int64_t s4 = 2097151 & (load_4(s + 10) >> 4);
  int64_t s5 = 2097151 & (load_3(s + 13) >> 1);
  int64_t s6 = 2097151 & (load_4(s + 15) >> 6);
  int64_t s7 = 2097151 & (load_3(s + 18) >> 3);
  int64_t s8 = 2097151 & load_3(s + 21);
  int64_t s9 = 2097151 & (load_4(s + 23) >> 5);
  int64_t s10 = 2097151 & (load_3(s + 26) >> 2);
  int64_t s11 = 2097151 & (load_4(s + 28) >> 7);
  int64_t s12 = 2097151 & (load_4(s + 31) >> 4);
  int64_t s13 = 2097151 & (load_3(s + 34) >> 1);
  int64_t s14 = 2097151 & (load_4(s + 36) >> 6);
  int64_t s15 = 2097151 & (load_3(s + 39) >> 3);
  int64_t s16 = 2097151 & load_3(s + 42);
  int64_t s17 = 2097151 & (load_4(s + 44) >> 5);
  int64_t s18 = 2097151 & (load_3(s + 47) >> 2);
  int64_t s19 = 2097151 & (load_4(s + 49) >> 7);
  int64_t s20 = 2097151 & (load_4(s + 52) >> 4);
  int64_t s21 = 2097151 & (load_3(s + 55) >> 1);
  int64_t s22 = 2097151 & (load_4(s + 57) >> 6);
  int64_t s23 = (load_4(s + 60) >> 3);
  int64_t carry0;
  int64_t carry1;
  int64_t carry2;
  int64_t carry3;
  int64_t carry4;
  int64_t carry5;
  int64_t carry6;
  int64_t carry7;
  int64_t carry8;
  int64_t carry9;
  int64_t carry10;
  int64_t carry11;
  int64_t carry12;
  int64_t carry13;
  int64_t carry14;
  int64_t carry15;
  int64_t carry16;
  s11 += s23 * 666643;
  s12 += s23 * 470296;
  s13 += s23 * 654183;
  s14 -= s23 * 997805;
  s15 += s23 * 136657;
  s16 -= s23 * 683901;
  s23 = 0;
  s10 += s22 * 666643;
  s11 += s22 * 470296;
  s12 += s22 * 654183;
  s13 -= s22 * 997805;
  s14 += s22 * 136657;
  s15 -= s22 * 683901;
  s22 = 0;
  s9 += s21 * 666643;
  s10 += s21 * 470296;
  s11 += s21 * 654183;
  s12 -= s21 * 997805;
  s13 += s21 * 136657;
  s14 -= s21 * 683901;
  s21 = 0;
  s8 += s20 * 666643;
  s9 += s20 * 470296;
  s10 += s20 * 654183;
  s11 -= s20 * 997805;
  s12 += s20 * 136657;
  s13 -= s20 * 683901;
  s20 = 0;
  s7 += s19 * 666643;
  s8 += s19 * 470296;
  s9 += s19 * 654183;
  s10 -= s19 * 997805;
  s11 += s19 * 136657;
  s12 -= s19 * 683901;
  s19 = 0;
  s6 += s18 * 666643;
  s7 += s18 * 470296;
  s8 += s18 * 654183;
  s9 -= s18 * 997805;
  s10 += s18 * 136657;
  s11 -= s18 * 683901;
  s18 = 0;
  carry6 = (s6 + (1 << 20)) >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry8 = (s8 + (1 << 20)) >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry10 = (s10 + (1 << 20)) >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry12 = (s12 + (1 << 20)) >> 21;
  s13 += carry12;
  s12 -= int64_lshift21(carry12);
  carry14 = (s14 + (1 << 20)) >> 21;
  s15 += carry14;
  s14 -= int64_lshift21(carry14);
  carry16 = (s16 + (1 << 20)) >> 21;
  s17 += carry16;
  s16 -= int64_lshift21(carry16);
  carry7 = (s7 + (1 << 20)) >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry9 = (s9 + (1 << 20)) >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry11 = (s11 + (1 << 20)) >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  carry13 = (s13 + (1 << 20)) >> 21;
  s14 += carry13;
  s13 -= int64_lshift21(carry13);
  carry15 = (s15 + (1 << 20)) >> 21;
  s16 += carry15;
  s15 -= int64_lshift21(carry15);
  s5 += s17 * 666643;
  s6 += s17 * 470296;
  s7 += s17 * 654183;
  s8 -= s17 * 997805;
  s9 += s17 * 136657;
  s10 -= s17 * 683901;
  s17 = 0;
  s4 += s16 * 666643;
  s5 += s16 * 470296;
  s6 += s16 * 654183;
  s7 -= s16 * 997805;
  s8 += s16 * 136657;
  s9 -= s16 * 683901;
  s16 = 0;
  s3 += s15 * 666643;
  s4 += s15 * 470296;
  s5 += s15 * 654183;
  s6 -= s15 * 997805;
  s7 += s15 * 136657;
  s8 -= s15 * 683901;
  s15 = 0;
  s2 += s14 * 666643;
  s3 += s14 * 470296;
  s4 += s14 * 654183;
  s5 -= s14 * 997805;
  s6 += s14 * 136657;
  s7 -= s14 * 683901;
  s14 = 0;
  s1 += s13 * 666643;
  s2 += s13 * 470296;
  s3 += s13 * 654183;
  s4 -= s13 * 997805;
  s5 += s13 * 136657;
  s6 -= s13 * 683901;
  s13 = 0;
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = (s0 + (1 << 20)) >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry2 = (s2 + (1 << 20)) >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry4 = (s4 + (1 << 20)) >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry6 = (s6 + (1 << 20)) >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry8 = (s8 + (1 << 20)) >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry10 = (s10 + (1 << 20)) >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry1 = (s1 + (1 << 20)) >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry3 = (s3 + (1 << 20)) >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry5 = (s5 + (1 << 20)) >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry7 = (s7 + (1 << 20)) >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry9 = (s9 + (1 << 20)) >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry11 = (s11 + (1 << 20)) >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = s0 >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry1 = s1 >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry2 = s2 >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry3 = s3 >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry4 = s4 >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry5 = s5 >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry6 = s6 >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry7 = s7 >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry8 = s8 >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry9 = s9 >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry10 = s10 >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry11 = s11 >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = s0 >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry1 = s1 >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry2 = s2 >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry3 = s3 >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry4 = s4 >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry5 = s5 >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry6 = s6 >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry7 = s7 >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry8 = s8 >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry9 = s9 >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry10 = s10 >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  s[0] = s0 >> 0;
  s[1] = s0 >> 8;
  s[2] = (s0 >> 16) | (s1 << 5);
  s[3] = s1 >> 3;
  s[4] = s1 >> 11;
  s[5] = (s1 >> 19) | (s2 << 2);
  s[6] = s2 >> 6;
  s[7] = (s2 >> 14) | (s3 << 7);
  s[8] = s3 >> 1;
  s[9] = s3 >> 9;
  s[10] = (s3 >> 17) | (s4 << 4);
  s[11] = s4 >> 4;
  s[12] = s4 >> 12;
  s[13] = (s4 >> 20) | (s5 << 1);
  s[14] = s5 >> 7;
  s[15] = (s5 >> 15) | (s6 << 6);
  s[16] = s6 >> 2;
  s[17] = s6 >> 10;
  s[18] = (s6 >> 18) | (s7 << 3);
  s[19] = s7 >> 5;
  s[20] = s7 >> 13;
  s[21] = s8 >> 0;
  s[22] = s8 >> 8;
  s[23] = (s8 >> 16) | (s9 << 5);
  s[24] = s9 >> 3;
  s[25] = s9 >> 11;
  s[26] = (s9 >> 19) | (s10 << 2);
  s[27] = s10 >> 6;
  s[28] = (s10 >> 14) | (s11 << 7);
  s[29] = s11 >> 1;
  s[30] = s11 >> 9;
  s[31] = s11 >> 17;
}
// Input:
//   a[0]+256*a[1]+...+256^31*a[31] = a
//   b[0]+256*b[1]+...+256^31*b[31] = b
//   c[0]+256*c[1]+...+256^31*c[31] = c
//
// Output:
//   s[0]+256*s[1]+...+256^31*s[31] = (ab+c) mod l
//   where l = 2^252 + 27742317777372353535851937790883648493.
static void sc_muladd(uint8_t *s, const uint8_t *a, const uint8_t *b,
                      const uint8_t *c) {
  int64_t a0 = 2097151 & load_3(a);
  int64_t a1 = 2097151 & (load_4(a + 2) >> 5);
  int64_t a2 = 2097151 & (load_3(a + 5) >> 2);
  int64_t a3 = 2097151 & (load_4(a + 7) >> 7);
  int64_t a4 = 2097151 & (load_4(a + 10) >> 4);
  int64_t a5 = 2097151 & (load_3(a + 13) >> 1);
  int64_t a6 = 2097151 & (load_4(a + 15) >> 6);
  int64_t a7 = 2097151 & (load_3(a + 18) >> 3);
  int64_t a8 = 2097151 & load_3(a + 21);
  int64_t a9 = 2097151 & (load_4(a + 23) >> 5);
  int64_t a10 = 2097151 & (load_3(a + 26) >> 2);
  int64_t a11 = (load_4(a + 28) >> 7);
  int64_t b0 = 2097151 & load_3(b);
  int64_t b1 = 2097151 & (load_4(b + 2) >> 5);
  int64_t b2 = 2097151 & (load_3(b + 5) >> 2);
  int64_t b3 = 2097151 & (load_4(b + 7) >> 7);
  int64_t b4 = 2097151 & (load_4(b + 10) >> 4);
  int64_t b5 = 2097151 & (load_3(b + 13) >> 1);
  int64_t b6 = 2097151 & (load_4(b + 15) >> 6);
  int64_t b7 = 2097151 & (load_3(b + 18) >> 3);
  int64_t b8 = 2097151 & load_3(b + 21);
  int64_t b9 = 2097151 & (load_4(b + 23) >> 5);
  int64_t b10 = 2097151 & (load_3(b + 26) >> 2);
  int64_t b11 = (load_4(b + 28) >> 7);
  int64_t c0 = 2097151 & load_3(c);
  int64_t c1 = 2097151 & (load_4(c + 2) >> 5);
  int64_t c2 = 2097151 & (load_3(c + 5) >> 2);
  int64_t c3 = 2097151 & (load_4(c + 7) >> 7);
  int64_t c4 = 2097151 & (load_4(c + 10) >> 4);
  int64_t c5 = 2097151 & (load_3(c + 13) >> 1);
  int64_t c6 = 2097151 & (load_4(c + 15) >> 6);
  int64_t c7 = 2097151 & (load_3(c + 18) >> 3);
  int64_t c8 = 2097151 & load_3(c + 21);
  int64_t c9 = 2097151 & (load_4(c + 23) >> 5);
  int64_t c10 = 2097151 & (load_3(c + 26) >> 2);
  int64_t c11 = (load_4(c + 28) >> 7);
  int64_t s0;
  int64_t s1;
  int64_t s2;
  int64_t s3;
  int64_t s4;
  int64_t s5;
  int64_t s6;
  int64_t s7;
  int64_t s8;
  int64_t s9;
  int64_t s10;
  int64_t s11;
  int64_t s12;
  int64_t s13;
  int64_t s14;
  int64_t s15;
  int64_t s16;
  int64_t s17;
  int64_t s18;
  int64_t s19;
  int64_t s20;
  int64_t s21;
  int64_t s22;
  int64_t s23;
  int64_t carry0;
  int64_t carry1;
  int64_t carry2;
  int64_t carry3;
  int64_t carry4;
  int64_t carry5;
  int64_t carry6;
  int64_t carry7;
  int64_t carry8;
  int64_t carry9;
  int64_t carry10;
  int64_t carry11;
  int64_t carry12;
  int64_t carry13;
  int64_t carry14;
  int64_t carry15;
  int64_t carry16;
  int64_t carry17;
  int64_t carry18;
  int64_t carry19;
  int64_t carry20;
  int64_t carry21;
  int64_t carry22;
  s0 = c0 + a0 * b0;
  s1 = c1 + a0 * b1 + a1 * b0;
  s2 = c2 + a0 * b2 + a1 * b1 + a2 * b0;
  s3 = c3 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
  s4 = c4 + a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;
  s5 = c5 + a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0;
  s6 = c6 + a0 * b6 + a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1 + a6 * b0;
  s7 = c7 + a0 * b7 + a1 * b6 + a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2 +
       a6 * b1 + a7 * b0;
  s8 = c8 + a0 * b8 + a1 * b7 + a2 * b6 + a3 * b5 + a4 * b4 + a5 * b3 +
       a6 * b2 + a7 * b1 + a8 * b0;
  s9 = c9 + a0 * b9 + a1 * b8 + a2 * b7 + a3 * b6 + a4 * b5 + a5 * b4 +
       a6 * b3 + a7 * b2 + a8 * b1 + a9 * b0;
  s10 = c10 + a0 * b10 + a1 * b9 + a2 * b8 + a3 * b7 + a4 * b6 + a5 * b5 +
        a6 * b4 + a7 * b3 + a8 * b2 + a9 * b1 + a10 * b0;
  s11 = c11 + a0 * b11 + a1 * b10 + a2 * b9 + a3 * b8 + a4 * b7 + a5 * b6 +
        a6 * b5 + a7 * b4 + a8 * b3 + a9 * b2 + a10 * b1 + a11 * b0;
  s12 = a1 * b11 + a2 * b10 + a3 * b9 + a4 * b8 + a5 * b7 + a6 * b6 + a7 * b5 +
        a8 * b4 + a9 * b3 + a10 * b2 + a11 * b1;
  s13 = a2 * b11 + a3 * b10 + a4 * b9 + a5 * b8 + a6 * b7 + a7 * b6 + a8 * b5 +
        a9 * b4 + a10 * b3 + a11 * b2;
  s14 = a3 * b11 + a4 * b10 + a5 * b9 + a6 * b8 + a7 * b7 + a8 * b6 + a9 * b5 +
        a10 * b4 + a11 * b3;
  s15 = a4 * b11 + a5 * b10 + a6 * b9 + a7 * b8 + a8 * b7 + a9 * b6 + a10 * b5 +
        a11 * b4;
  s16 = a5 * b11 + a6 * b10 + a7 * b9 + a8 * b8 + a9 * b7 + a10 * b6 + a11 * b5;
  s17 = a6 * b11 + a7 * b10 + a8 * b9 + a9 * b8 + a10 * b7 + a11 * b6;
  s18 = a7 * b11 + a8 * b10 + a9 * b9 + a10 * b8 + a11 * b7;
  s19 = a8 * b11 + a9 * b10 + a10 * b9 + a11 * b8;
  s20 = a9 * b11 + a10 * b10 + a11 * b9;
  s21 = a10 * b11 + a11 * b10;
  s22 = a11 * b11;
  s23 = 0;
  carry0 = (s0 + (1 << 20)) >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry2 = (s2 + (1 << 20)) >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry4 = (s4 + (1 << 20)) >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry6 = (s6 + (1 << 20)) >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry8 = (s8 + (1 << 20)) >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry10 = (s10 + (1 << 20)) >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry12 = (s12 + (1 << 20)) >> 21;
  s13 += carry12;
  s12 -= int64_lshift21(carry12);
  carry14 = (s14 + (1 << 20)) >> 21;
  s15 += carry14;
  s14 -= int64_lshift21(carry14);
  carry16 = (s16 + (1 << 20)) >> 21;
  s17 += carry16;
  s16 -= int64_lshift21(carry16);
  carry18 = (s18 + (1 << 20)) >> 21;
  s19 += carry18;
  s18 -= int64_lshift21(carry18);
  carry20 = (s20 + (1 << 20)) >> 21;
  s21 += carry20;
  s20 -= int64_lshift21(carry20);
  carry22 = (s22 + (1 << 20)) >> 21;
  s23 += carry22;
  s22 -= int64_lshift21(carry22);
  carry1 = (s1 + (1 << 20)) >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry3 = (s3 + (1 << 20)) >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry5 = (s5 + (1 << 20)) >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry7 = (s7 + (1 << 20)) >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry9 = (s9 + (1 << 20)) >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry11 = (s11 + (1 << 20)) >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  carry13 = (s13 + (1 << 20)) >> 21;
  s14 += carry13;
  s13 -= int64_lshift21(carry13);
  carry15 = (s15 + (1 << 20)) >> 21;
  s16 += carry15;
  s15 -= int64_lshift21(carry15);
  carry17 = (s17 + (1 << 20)) >> 21;
  s18 += carry17;
  s17 -= int64_lshift21(carry17);
  carry19 = (s19 + (1 << 20)) >> 21;
  s20 += carry19;
  s19 -= int64_lshift21(carry19);
  carry21 = (s21 + (1 << 20)) >> 21;
  s22 += carry21;
  s21 -= int64_lshift21(carry21);
  s11 += s23 * 666643;
  s12 += s23 * 470296;
  s13 += s23 * 654183;
  s14 -= s23 * 997805;
  s15 += s23 * 136657;
  s16 -= s23 * 683901;
  s23 = 0;
  s10 += s22 * 666643;
  s11 += s22 * 470296;
  s12 += s22 * 654183;
  s13 -= s22 * 997805;
  s14 += s22 * 136657;
  s15 -= s22 * 683901;
  s22 = 0;
  s9 += s21 * 666643;
  s10 += s21 * 470296;
  s11 += s21 * 654183;
  s12 -= s21 * 997805;
  s13 += s21 * 136657;
  s14 -= s21 * 683901;
  s21 = 0;
  s8 += s20 * 666643;
  s9 += s20 * 470296;
  s10 += s20 * 654183;
  s11 -= s20 * 997805;
  s12 += s20 * 136657;
  s13 -= s20 * 683901;
  s20 = 0;
  s7 += s19 * 666643;
  s8 += s19 * 470296;
  s9 += s19 * 654183;
  s10 -= s19 * 997805;
  s11 += s19 * 136657;
  s12 -= s19 * 683901;
  s19 = 0;
  s6 += s18 * 666643;
  s7 += s18 * 470296;
  s8 += s18 * 654183;
  s9 -= s18 * 997805;
  s10 += s18 * 136657;
  s11 -= s18 * 683901;
  s18 = 0;
  carry6 = (s6 + (1 << 20)) >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry8 = (s8 + (1 << 20)) >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry10 = (s10 + (1 << 20)) >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry12 = (s12 + (1 << 20)) >> 21;
  s13 += carry12;
  s12 -= int64_lshift21(carry12);
  carry14 = (s14 + (1 << 20)) >> 21;
  s15 += carry14;
  s14 -= int64_lshift21(carry14);
  carry16 = (s16 + (1 << 20)) >> 21;
  s17 += carry16;
  s16 -= int64_lshift21(carry16);
  carry7 = (s7 + (1 << 20)) >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry9 = (s9 + (1 << 20)) >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry11 = (s11 + (1 << 20)) >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  carry13 = (s13 + (1 << 20)) >> 21;
  s14 += carry13;
  s13 -= int64_lshift21(carry13);
  carry15 = (s15 + (1 << 20)) >> 21;
  s16 += carry15;
  s15 -= int64_lshift21(carry15);
  s5 += s17 * 666643;
  s6 += s17 * 470296;
  s7 += s17 * 654183;
  s8 -= s17 * 997805;
  s9 += s17 * 136657;
  s10 -= s17 * 683901;
  s17 = 0;
  s4 += s16 * 666643;
  s5 += s16 * 470296;
  s6 += s16 * 654183;
  s7 -= s16 * 997805;
  s8 += s16 * 136657;
  s9 -= s16 * 683901;
  s16 = 0;
  s3 += s15 * 666643;
  s4 += s15 * 470296;
  s5 += s15 * 654183;
  s6 -= s15 * 997805;
  s7 += s15 * 136657;
  s8 -= s15 * 683901;
  s15 = 0;
  s2 += s14 * 666643;
  s3 += s14 * 470296;
  s4 += s14 * 654183;
  s5 -= s14 * 997805;
  s6 += s14 * 136657;
  s7 -= s14 * 683901;
  s14 = 0;
  s1 += s13 * 666643;
  s2 += s13 * 470296;
  s3 += s13 * 654183;
  s4 -= s13 * 997805;
  s5 += s13 * 136657;
  s6 -= s13 * 683901;
  s13 = 0;
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = (s0 + (1 << 20)) >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry2 = (s2 + (1 << 20)) >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry4 = (s4 + (1 << 20)) >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry6 = (s6 + (1 << 20)) >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry8 = (s8 + (1 << 20)) >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry10 = (s10 + (1 << 20)) >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry1 = (s1 + (1 << 20)) >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry3 = (s3 + (1 << 20)) >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry5 = (s5 + (1 << 20)) >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry7 = (s7 + (1 << 20)) >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry9 = (s9 + (1 << 20)) >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry11 = (s11 + (1 << 20)) >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = s0 >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry1 = s1 >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry2 = s2 >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry3 = s3 >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry4 = s4 >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry5 = s5 >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry6 = s6 >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry7 = s7 >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry8 = s8 >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry9 = s9 >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry10 = s10 >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  carry11 = s11 >> 21;
  s12 += carry11;
  s11 -= int64_lshift21(carry11);
  s0 += s12 * 666643;
  s1 += s12 * 470296;
  s2 += s12 * 654183;
  s3 -= s12 * 997805;
  s4 += s12 * 136657;
  s5 -= s12 * 683901;
  s12 = 0;
  carry0 = s0 >> 21;
  s1 += carry0;
  s0 -= int64_lshift21(carry0);
  carry1 = s1 >> 21;
  s2 += carry1;
  s1 -= int64_lshift21(carry1);
  carry2 = s2 >> 21;
  s3 += carry2;
  s2 -= int64_lshift21(carry2);
  carry3 = s3 >> 21;
  s4 += carry3;
  s3 -= int64_lshift21(carry3);
  carry4 = s4 >> 21;
  s5 += carry4;
  s4 -= int64_lshift21(carry4);
  carry5 = s5 >> 21;
  s6 += carry5;
  s5 -= int64_lshift21(carry5);
  carry6 = s6 >> 21;
  s7 += carry6;
  s6 -= int64_lshift21(carry6);
  carry7 = s7 >> 21;
  s8 += carry7;
  s7 -= int64_lshift21(carry7);
  carry8 = s8 >> 21;
  s9 += carry8;
  s8 -= int64_lshift21(carry8);
  carry9 = s9 >> 21;
  s10 += carry9;
  s9 -= int64_lshift21(carry9);
  carry10 = s10 >> 21;
  s11 += carry10;
  s10 -= int64_lshift21(carry10);
  s[0] = s0 >> 0;
  s[1] = s0 >> 8;
  s[2] = (s0 >> 16) | (s1 << 5);
  s[3] = s1 >> 3;
  s[4] = s1 >> 11;
  s[5] = (s1 >> 19) | (s2 << 2);
  s[6] = s2 >> 6;
  s[7] = (s2 >> 14) | (s3 << 7);
  s[8] = s3 >> 1;
  s[9] = s3 >> 9;
  s[10] = (s3 >> 17) | (s4 << 4);
  s[11] = s4 >> 4;
  s[12] = s4 >> 12;
  s[13] = (s4 >> 20) | (s5 << 1);
  s[14] = s5 >> 7;
  s[15] = (s5 >> 15) | (s6 << 6);
  s[16] = s6 >> 2;
  s[17] = s6 >> 10;
  s[18] = (s6 >> 18) | (s7 << 3);
  s[19] = s7 >> 5;
  s[20] = s7 >> 13;
  s[21] = s8 >> 0;
  s[22] = s8 >> 8;
  s[23] = (s8 >> 16) | (s9 << 5);
  s[24] = s9 >> 3;
  s[25] = s9 >> 11;
  s[26] = (s9 >> 19) | (s10 << 2);
  s[27] = s10 >> 6;
  s[28] = (s10 >> 14) | (s11 << 7);
  s[29] = s11 >> 1;
  s[30] = s11 >> 9;
  s[31] = s11 >> 17;
}
static void X25519_public_from_private(uint8_t out_public_value[32],
                                const uint8_t private_key[32]) {
  uint8_t e[32];
  memcpy(e, private_key, 32);
  e[0] &= 248;
  e[31] &= 127;
  e[31] |= 64;
  ge_p3 A;
  x25519_ge_scalarmult_base(&A, e);
  // We only need the u-coordinate of the curve25519 point. The map is
  // u=(y+1)/(1-y). Since y=Y/Z, this gives u=(Z+Y)/(Z-Y).
  fe_loose zplusy, zminusy;
  fe zminusy_inv;
  fe_add(&zplusy, &A.Z, &A.Y);
  fe_sub(&zminusy, &A.Z, &A.Y);
  fe_loose_invert(&zminusy_inv, &zminusy);
  fe_mul_tlt(&zminusy_inv, &zplusy, &zminusy_inv);
  fe_tobytes(out_public_value, &zminusy_inv);
}

void ED25519_keypair_from_seed(uint8_t out_public_key[32],
                               uint8_t out_private_key[64],
                               const uint8_t seed[32]) {
  uint8_t az[SHA512_DIGEST_LENGTH];
  SHA512(seed, 32, az);

  az[0] &= 248;
  az[31] &= 127;
  az[31] |= 64;

  ge_p3 A;
  x25519_ge_scalarmult_base(&A, az);
  ge_p3_tobytes(out_public_key, &A);

  memcpy(out_private_key, seed, 32);
  memcpy(out_private_key + 32, out_public_key, 32);
}
static int ED25519_sign(uint8_t out_sig[64], const uint8_t *message,
                 size_t message_len, const uint8_t private_key[64]) {
  // NOTE: The documentation on this function says that it returns zero on
  // allocation failure. While that can't happen with the current
  // implementation, we want to reserve the ability to allocate in this
  // implementation in the future.
  uint8_t az[SHA512_DIGEST_LENGTH];
  SHA512(private_key, 32, az);
  az[0] &= 248;
  az[31] &= 63;
  az[31] |= 64;
  SHA512_CTX hash_ctx;
  SHA512_Init(&hash_ctx);
  SHA512_Update(&hash_ctx, az + 32, 32);
  SHA512_Update(&hash_ctx, message, message_len);
  uint8_t nonce[SHA512_DIGEST_LENGTH];
  SHA512_Final(nonce, &hash_ctx);
  x25519_sc_reduce(nonce);
  ge_p3 R;
  x25519_ge_scalarmult_base(&R, nonce);
  ge_p3_tobytes(out_sig, &R);
  SHA512_Init(&hash_ctx);
  SHA512_Update(&hash_ctx, out_sig, 32);
  SHA512_Update(&hash_ctx, private_key + 32, 32);
  SHA512_Update(&hash_ctx, message, message_len);
  uint8_t hram[SHA512_DIGEST_LENGTH];
  SHA512_Final(hram, &hash_ctx);
  x25519_sc_reduce(hram);
  sc_muladd(out_sig + 32, hram, az, nonce);
  return 1;
}
#include <stdio.h>
int main() {
        // https://www.rfc-editor.org/rfc/rfc8032.txt TEST 3
        uint8_t sk[32] = {0xc5,0xaa,0x8d,0xf4,0x3f,0x9f,0x83,0x7b,0xed,0xb7,0x44,0x2f,0x31,0xdc,0xb7,0xb1,0x66,0xd3,0x85,0x35,0x07,0x6f,0x09,0x4b,0x85,0xce,0x3a,0x2e,0x0b,0x44,0x58,0xf7};
        uint8_t az[64], pk[32];
        ED25519_keypair_from_seed(pk, az, sk);
        for (int i = 0; i<sizeof(pk); i++) { printf("%02x", pk[i]); } printf("\n");
        uint8_t msg[2] = {0xaf, 0x82};
        uint8_t sig[64];
        if (!ED25519_sign(sig, msg, sizeof(msg), az)) {
                return 1;
        }
        for (int i = 0; i<sizeof(sig); i++) { printf("%02x", sig[i]); } printf("\n");

        uint8_t pk_ref[] = {0xfc,0x51,0xcd,0x8e,0x62,0x18,0xa1,0xa3,0x8d,0xa4,0x7e,0xd0,0x02,0x30,0xf0,0x58,0x08,0x16,0xed,0x13,0xba,0x33,0x03,0xac,0x5d,0xeb,0x91,0x15,0x48,0x90,0x80,0x25};
        for (int i = 0; i<sizeof(pk); i++) if (pk[i] != pk_ref[i]) return 1+i;
        uint8_t sig_ref[] = {0x62,0x91,0xd6,0x57,0xde,0xec,0x24,0x02,0x48,0x27,0xe6,0x9c,0x3a,0xbe,0x01,0xa3,0x0c,0xe5,0x48,0xa2,0x84,0x74,0x3a,0x44,0x5e,0x36,0x80,0xd7,0xdb,0x5a,0xc3,0xac,0x18,0xff,0x9b,0x53,0x8d,0x16,0xf2,0x90,0xae,0x67,0xf7,0x60,0x98,0x4d,0xc6,0x59,0x4a,0x7c,0x15,0xe9,0x71,0x6e,0xd2,0x8d,0xc0,0x27,0xbe,0xce,0xea,0x1e,0xc4,0x0a};
        for (int i = 0; i<sizeof(sig); i++) if (sig[i] != sig_ref[i]) return 1+sizeof(pk)+i;
        printf("pass\n");
}
