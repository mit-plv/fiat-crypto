#!/bin/bash
set -euo pipefail

cat << 'EOF'
// The non-synthesized parts are from Adam Langley's curve25519-donna-c64
// (Copytight 2008 Google, released into public domain)
#include <stdint.h>
#include <string.h>
#include "crypto_scalarmult.h"
typedef uint64_t fe25519[5];
typedef unsigned uint128_t __attribute__((mode(TI)));

static void
fmul(fe25519 output, const fe25519 in2, const fe25519 in) {
EOF

< src/Specific/IntegrationTestMulDisplay.log \
  grep -- "λ '(" | \
  grep -owP -- 'x\d+' | \
  paste -d ' =;' \
    <(for i in $(seq 1 10); do echo uint64_t; done) \
    /dev/stdin \
    <(echo {in2,in}\[{4,3,2,1,0}\] | tr ' ' '\n') \
    /dev/null

< src/Specific/IntegrationTestMulDisplay.log \
grep -oP 'uint\d+_t\W+\w+ = .*;$'

< src/Specific/IntegrationTestMulDisplay.log \
  grep -- Return | \
  grep -owP -- 'x\d+' | \
  paste -d '=;' \
    <(echo output\[{4,3,2,1,0}\] | tr ' ' '\n') \
    /dev/stdin \
    /dev/null

cat << 'EOF'
}

static void
fsquare_times(fe25519 output, const fe25519 in, uint64_t count) {
  uint64_t r0,r1,r2,r3,r4;

  r0 = in[0];
  r1 = in[1];
  r2 = in[2];
  r3 = in[3];
  r4 = in[4];

  do {
EOF

< src/Specific/IntegrationTestSquareDisplay.log \
  grep -- "λ '(" | \
  grep -owP -- 'x\d+' | \
  paste -d ' =;' \
    <(for i in $(seq 1 5); do echo uint64_t; done) \
    /dev/stdin \
    <(echo r{4,3,2,1,0} | tr ' ' '\n') \
    /dev/null

< src/Specific/IntegrationTestSquareDisplay.log \
grep -oP 'uint\d+_t\W+\w+ = .*;$'

< src/Specific/IntegrationTestSquareDisplay.log \
  grep -- Return | \
  grep -owP -- 'x\d+' | \
  paste -d '=;' \
    <(echo r{4,3,2,1,0} | tr ' ' '\n') \
    /dev/stdin \
    /dev/null

cat << 'EOF'
  } while(--count);

  output[0] = r0;
  output[1] = r1;
  output[2] = r2;
  output[3] = r3;
  output[4] = r4;
}

/* Input: Q, Q', Q-Q'
 * Output: 2Q, Q+Q' */
static void
fmonty(uint64_t *x2, uint64_t *z2, /* output 2Q */
       uint64_t *x3, uint64_t *z3, /* output Q + Q' */
       uint64_t *x, uint64_t *z,   /* input Q */
       uint64_t *xprime, uint64_t *zprime, /* input Q' */
       const uint64_t *qmqp /* input Q - Q' */) {
EOF

< src/Specific/IntegrationTestLadderstepDisplay.log \
  grep -- "λ '(" | \
  grep -owP -- 'x\d+' | \
  paste -d ' =;' \
    <(for i in $(seq 1 25); do echo uint64_t; done) \
    /dev/stdin \
    <(echo {qmqp,x,z,xprime,zprime}\[{4,3,2,1,0}\] | tr ' ' '\n') \
    /dev/null

< src/Specific/IntegrationTestLadderstepDisplay.log \
grep -oP 'uint\d+_t\W+\w+ = .*;$'

< src/Specific/IntegrationTestLadderstepDisplay.log \
  grep -- Return | \
  grep -owP -- 'x\d+' | \
  paste -d '=;' \
    <(echo {x2,z2,x3,z3}\[{4,3,2,1,0}\] | tr ' ' '\n') \
    /dev/stdin \
    /dev/null

cat <<'EOF'
}

/* Take a little-endian, 32-byte number and expand it into polynomial form */
static void
fexpand(uint64_t *output, const uint8_t *in) {
  output[0] = *((const uint64_t *)(in)) & 0x7ffffffffffff;
  output[1] = (*((const uint64_t *)(in+6)) >> 3) & 0x7ffffffffffff;
  output[2] = (*((const uint64_t *)(in+12)) >> 6) & 0x7ffffffffffff;
  output[3] = (*((const uint64_t *)(in+19)) >> 1) & 0x7ffffffffffff;
  output[4] = (*((const uint64_t *)(in+25)) >> 4) & 0x7ffffffffffff;
}

/* Take a fully reduced polynomial form number and contract it into a
 * little-endian, 32-byte array */
static void
fcontract(uint8_t *output, const fe25519 input) {
  uint128_t t[5];

  t[0] = input[0];
  t[1] = input[1];
  t[2] = input[2];
  t[3] = input[3];
  t[4] = input[4];

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now t is between 0 and 2^255-1, properly carried. */
  /* case 1: between 0 and 2^255-20. case 2: between 2^255-19 and 2^255-1. */

  t[0] += 19;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now between 19 and 2^255-1 in both cases, and offset by 19. */

  t[0] += 0x8000000000000 - 19;
  t[1] += 0x8000000000000 - 1;
  t[2] += 0x8000000000000 - 1;
  t[3] += 0x8000000000000 - 1;
  t[4] += 0x8000000000000 - 1;

  /* now between 2^255 and 2^256-20, and offset by 2^255. */

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[4] &= 0x7ffffffffffff;

  *((uint64_t *)(output)) = t[0] | (t[1] << 51);
  *((uint64_t *)(output+8)) = (t[1] >> 13) | (t[2] << 38);
  *((uint64_t *)(output+16)) = (t[2] >> 26) | (t[3] << 25);
  *((uint64_t *)(output+24)) = (t[3] >> 39) | (t[4] << 12);
}

// -----------------------------------------------------------------------------
// Maybe swap the contents of two uint64_t arrays (@a and @b), each @len elements
// long. Perform the swap iff @swap is non-zero.
//
// This function performs the swap without leaking any side-channel
// information.
// -----------------------------------------------------------------------------
static void
swap_conditional(uint64_t a[5], uint64_t b[5], uint64_t iswap) {
  unsigned i;
  const uint64_t swap = -iswap;

  for (i = 0; i < 5; ++i) {
    const uint64_t x = swap & (a[i] ^ b[i]);
    a[i] ^= x;
    b[i] ^= x;
  }
}

/* Calculates nQ where Q is the x-coordinate of a point on the curve
 *
 *   resultx/resultz: the x coordinate of the resulting curve point (short form)
 *   n: a little endian, 32-byte number
 *   q: a point of the curve (short form)
 */
static void
cmult(uint64_t *resultx, uint64_t *resultz, const uint8_t *n, const uint64_t *q) {
  uint64_t a[5] = {0}, b[5] = {1}, c[5] = {1}, d[5] = {0};
  uint64_t *nqpqx = a, *nqpqz = b, *nqx = c, *nqz = d, *t;
  uint64_t e[5] = {0}, f[5] = {1}, g[5] = {0}, h[5] = {1};
  uint64_t *nqpqx2 = e, *nqpqz2 = f, *nqx2 = g, *nqz2 = h;

  unsigned i, j;

  memcpy(nqpqx, q, sizeof(uint64_t) * 5);

  for (i = 0; i < 32; ++i) {
    uint8_t byte = n[31 - i];
    for (j = 0; j < 8; ++j) {
      const uint64_t bit = byte >> 7;

      swap_conditional(nqx, nqpqx, bit);
      swap_conditional(nqz, nqpqz, bit);
      fmonty(nqx2, nqz2,
             nqpqx2, nqpqz2,
             nqx, nqz,
             nqpqx, nqpqz,
             q);
      swap_conditional(nqx2, nqpqx2, bit);
      swap_conditional(nqz2, nqpqz2, bit);

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

      byte <<= 1;
    }
  }

  memcpy(resultx, nqx, sizeof(uint64_t) * 5);
  memcpy(resultz, nqz, sizeof(uint64_t) * 5);
}


// -----------------------------------------------------------------------------
// Shamelessly copied from djb's code, tightened a little
// -----------------------------------------------------------------------------
static void
crecip(fe25519 out, const fe25519 z) {
  fe25519 a,t0,b,c;

  /* 2 */ fsquare_times(a, z, 1); // a = 2
  /* 8 */ fsquare_times(t0, a, 2);
  /* 9 */ fmul(b, t0, z); // b = 9
  /* 11 */ fmul(a, b, a); // a = 11
  /* 22 */ fsquare_times(t0, a, 1);
  /* 2^5 - 2^0 = 31 */ fmul(b, t0, b);
  /* 2^10 - 2^5 */ fsquare_times(t0, b, 5);
  /* 2^10 - 2^0 */ fmul(b, t0, b);
  /* 2^20 - 2^10 */ fsquare_times(t0, b, 10);
  /* 2^20 - 2^0 */ fmul(c, t0, b);
  /* 2^40 - 2^20 */ fsquare_times(t0, c, 20);
  /* 2^40 - 2^0 */ fmul(t0, t0, c);
  /* 2^50 - 2^10 */ fsquare_times(t0, t0, 10);
  /* 2^50 - 2^0 */ fmul(b, t0, b);
  /* 2^100 - 2^50 */ fsquare_times(t0, b, 50);
  /* 2^100 - 2^0 */ fmul(c, t0, b);
  /* 2^200 - 2^100 */ fsquare_times(t0, c, 100);
  /* 2^200 - 2^0 */ fmul(t0, t0, c);
  /* 2^250 - 2^50 */ fsquare_times(t0, t0, 50);
  /* 2^250 - 2^0 */ fmul(t0, t0, b);
  /* 2^255 - 2^5 */ fsquare_times(t0, t0, 5);
  /* 2^255 - 21 */ fmul(out, t0, a);
}

int
crypto_scalarmult(uint8_t *mypublic, const uint8_t *secret, const uint8_t *basepoint) {
  uint64_t bp[5], x[5], z[5], zmone[5];
  uint8_t e[32];
  int i;

  for (i = 0;i < 32;++i) e[i] = secret[i];
  e[0] &= 248;
  e[31] &= 127;
  e[31] |= 64;

  fexpand(bp, basepoint);
  cmult(x, z, e, bp);
  crecip(zmone, z);
  fmul(z, x, zmone);
  fcontract(mypublic, z);
  return 0;
}
EOF
