/*
 * Copyright 2011-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

/* Copyright 2011 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 *
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

/*
 * A 64-bit implementation of the NIST P-256 elliptic curve point multiplication
 *
 * OpenSSL integration was taken from Emilia Kasper's work in ecp_nistp224.c.
 * Otherwise based on Emilia's P224 work, which was inspired by my curve25519
 * work which got its smarts from Daniel J. Bernstein's work on the same.
 */

# include <stdint.h>
# include <string.h>
# include <openssl/err.h>
# include "ecp_nistp256.h"


/*
 * These are the parameters of P256, taken from FIPS 186-3, page 86. These
 * values are big-endian.
 */
static const felem_bytearray nistp256_curve_params[5] = {
    {0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, /* p */
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff},
    {0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, /* a = -3 */
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfc}, /* b */
    {0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7,
     0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98, 0x86, 0xbc,
     0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6,
     0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2, 0x60, 0x4b},
    {0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, /* x */
     0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40, 0xf2,
     0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0,
     0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2, 0x96},
    {0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b, /* y */
     0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e, 0x16,
     0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce,
     0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf, 0x51, 0xf5}
};

/*-

/* This is the value of the prime as four 64-bit words, little-endian. */
static const u64 kPrime[4] =
    { 0xfffffffffffffffful, 0xffffffff, 0, 0xffffffff00000001ul };
static const u64 bottom63bits = 0x7ffffffffffffffful;

/*
 * bin32_to_felem takes a little-endian byte array and converts it into felem
 * form. This assumes that the CPU is little-endian.
 */
static void bin32_to_felem(felem out, const u8 in[32])
{
    out[0] = *((u64 *)&in[0]);
    out[1] = *((u64 *)&in[8]);
    out[2] = *((u64 *)&in[16]);
    out[3] = *((u64 *)&in[24]);
}

/*
 * smallfelem_to_bin32 takes a smallfelem and serialises into a little
 * endian, 32 byte array. This assumes that the CPU is little-endian.
 */
static void smallfelem_to_bin32(u8 out[32], const smallfelem in)
{
    *((u64 *)&out[0]) = in[0];
    *((u64 *)&out[8]) = in[1];
    *((u64 *)&out[16]) = in[2];
    *((u64 *)&out[24]) = in[3];
}

/*-
 * Field operations
 * ----------------
 */

static void smallfelem_one(smallfelem out)
{
    out[0] = 1;
    out[1] = 0;
    out[2] = 0;
    out[3] = 0;
}

static void smallfelem_assign(smallfelem out, const smallfelem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
}

static void felem_assign(felem out, const felem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
}

/* felem_sum sets out = out + in. */
static void felem_sum(felem out, const felem in)
{
    out[0] += in[0];
    out[1] += in[1];
    out[2] += in[2];
    out[3] += in[3];
}

/* felem_small_sum sets out = out + in. */
static void felem_small_sum(felem out, const smallfelem in)
{
    out[0] += in[0];
    out[1] += in[1];
    out[2] += in[2];
    out[3] += in[3];
}

/* felem_scalar sets out = out * scalar */
static void felem_scalar(felem out, const u64 scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
}

/* longfelem_scalar sets out = out * scalar */
static void longfelem_scalar(longfelem out, const u64 scalar)
{
    out[0] *= scalar;
    out[1] *= scalar;
    out[2] *= scalar;
    out[3] *= scalar;
    out[4] *= scalar;
    out[5] *= scalar;
    out[6] *= scalar;
    out[7] *= scalar;
}

# define two105m41m9 (((limb)1) << 105) - (((limb)1) << 41) - (((limb)1) << 9)
# define two105 (((limb)1) << 105)
# define two105m41p9 (((limb)1) << 105) - (((limb)1) << 41) + (((limb)1) << 9)

/* zero105 is 0 mod p */
static const felem zero105 =
    { two105m41m9, two105, two105m41p9, two105m41p9 };

/*-
 * smallfelem_neg sets |out| to |-small|
 * On exit:
 *   out[i] < out[i] + 2^105
 */
static void smallfelem_neg(felem out, const smallfelem small)
{
    /* In order to prevent underflow, we subtract from 0 mod p. */
    out[0] = zero105[0] - small[0];
    out[1] = zero105[1] - small[1];
    out[2] = zero105[2] - small[2];
    out[3] = zero105[3] - small[3];
}

/*-
 * felem_diff subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^104
 * On exit:
 *   out[i] < out[i] + 2^105
 */
static void felem_diff(felem out, const felem in)
{
    /*
     * In order to prevent underflow, we add 0 mod p before subtracting.
     */
    out[0] += zero105[0];
    out[1] += zero105[1];
    out[2] += zero105[2];
    out[3] += zero105[3];

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}

# define two107m43m11 (((limb)1) << 107) - (((limb)1) << 43) - (((limb)1) << 11)
# define two107 (((limb)1) << 107)
# define two107m43p11 (((limb)1) << 107) - (((limb)1) << 43) + (((limb)1) << 11)

/* zero107 is 0 mod p */
static const felem zero107 =
    { two107m43m11, two107, two107m43p11, two107m43p11 };

/*-
 * An alternative felem_diff for larger inputs |in|
 * felem_diff_zero107 subtracts |in| from |out|
 * On entry:
 *   in[i] < 2^106
 * On exit:
 *   out[i] < out[i] + 2^107
 */
static void felem_diff_zero107(felem out, const felem in)
{
    /*
     * In order to prevent underflow, we add 0 mod p before subtracting.
     */
    out[0] += zero107[0];
    out[1] += zero107[1];
    out[2] += zero107[2];
    out[3] += zero107[3];

    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
}

/*-
 * longfelem_diff subtracts |in| from |out|
 * On entry:
 *   in[i] < 7*2^67
 * On exit:
 *   out[i] < out[i] + 2^70 + 2^40
 */
static void longfelem_diff(longfelem out, const longfelem in)
{
    static const limb two70m8p6 =
        (((limb) 1) << 70) - (((limb) 1) << 8) + (((limb) 1) << 6);
    static const limb two70p40 = (((limb) 1) << 70) + (((limb) 1) << 40);
    static const limb two70 = (((limb) 1) << 70);
    static const limb two70m40m38p6 =
        (((limb) 1) << 70) - (((limb) 1) << 40) - (((limb) 1) << 38) +
        (((limb) 1) << 6);
    static const limb two70m6 = (((limb) 1) << 70) - (((limb) 1) << 6);

    /* add 0 mod p to avoid underflow */
    out[0] += two70m8p6;
    out[1] += two70p40;
    out[2] += two70;
    out[3] += two70m40m38p6;
    out[4] += two70m6;
    out[5] += two70m6;
    out[6] += two70m6;
    out[7] += two70m6;

    /* in[i] < 7*2^67 < 2^70 - 2^40 - 2^38 + 2^6 */
    out[0] -= in[0];
    out[1] -= in[1];
    out[2] -= in[2];
    out[3] -= in[3];
    out[4] -= in[4];
    out[5] -= in[5];
    out[6] -= in[6];
    out[7] -= in[7];
}

# define two64m0 (((limb)1) << 64) - 1
# define two110p32m0 (((limb)1) << 110) + (((limb)1) << 32) - 1
# define two64m46 (((limb)1) << 64) - (((limb)1) << 46)
# define two64m32 (((limb)1) << 64) - (((limb)1) << 32)

/* zero110 is 0 mod p */
static const felem zero110 = { two64m0, two110p32m0, two64m46, two64m32 };

/*-
 * felem_shrink converts an felem into a smallfelem. The result isn't quite
 * minimal as the value may be greater than p.
 *
 * On entry:
 *   in[i] < 2^109
 * On exit:
 *   out[i] < 2^64
 */
static void felem_shrink(smallfelem out, const felem in)
{
    felem tmp;
    u64 a, b, mask;
    s64 high, low;
    static const u64 kPrime3Test = 0x7fffffff00000001ul; /* 2^63 - 2^32 + 1 */

    /* Carry 2->3 */
    tmp[3] = zero110[3] + in[3] + ((u64)(in[2] >> 64));
    /* tmp[3] < 2^110 */

    tmp[2] = zero110[2] + (u64)in[2];
    tmp[0] = zero110[0] + in[0];
    tmp[1] = zero110[1] + in[1];
    /* tmp[0] < 2**110, tmp[1] < 2^111, tmp[2] < 2**65 */

    /*
     * We perform two partial reductions where we eliminate the high-word of
     * tmp[3]. We don't update the other words till the end.
     */
    a = tmp[3] >> 64;           /* a < 2^46 */
    tmp[3] = (u64)tmp[3];
    tmp[3] -= a;
    tmp[3] += ((limb) a) << 32;
    /* tmp[3] < 2^79 */

    b = a;
    a = tmp[3] >> 64;           /* a < 2^15 */
    b += a;                     /* b < 2^46 + 2^15 < 2^47 */
    tmp[3] = (u64)tmp[3];
    tmp[3] -= a;
    tmp[3] += ((limb) a) << 32;
    /* tmp[3] < 2^64 + 2^47 */

    /*
     * This adjusts the other two words to complete the two partial
     * reductions.
     */
    tmp[0] += b;
    tmp[1] -= (((limb) b) << 32);

    /*
     * In order to make space in tmp[3] for the carry from 2 -> 3, we
     * conditionally subtract kPrime if tmp[3] is large enough.
     */
    high = tmp[3] >> 64;
    /* As tmp[3] < 2^65, high is either 1 or 0 */
    high <<= 63;
    high >>= 63;
    /*-
     * high is:
     *   all ones   if the high word of tmp[3] is 1
     *   all zeros  if the high word of tmp[3] if 0 */
    low = tmp[3];
    mask = low >> 63;
    /*-
     * mask is:
     *   all ones   if the MSB of low is 1
     *   all zeros  if the MSB of low if 0 */
    low &= bottom63bits;
    low -= kPrime3Test;
    /* if low was greater than kPrime3Test then the MSB is zero */
    low = ~low;
    low >>= 63;
    /*-
     * low is:
     *   all ones   if low was > kPrime3Test
     *   all zeros  if low was <= kPrime3Test */
    mask = (mask & low) | high;
    tmp[0] -= mask & kPrime[0];
    tmp[1] -= mask & kPrime[1];
    /* kPrime[2] is zero, so omitted */
    tmp[3] -= mask & kPrime[3];
    /* tmp[3] < 2**64 - 2**32 + 1 */

    tmp[1] += ((u64)(tmp[0] >> 64));
    tmp[0] = (u64)tmp[0];
    tmp[2] += ((u64)(tmp[1] >> 64));
    tmp[1] = (u64)tmp[1];
    tmp[3] += ((u64)(tmp[2] >> 64));
    tmp[2] = (u64)tmp[2];
    /* tmp[i] < 2^64 */

    out[0] = tmp[0];
    out[1] = tmp[1];
    out[2] = tmp[2];
    out[3] = tmp[3];
}

/* smallfelem_expand converts a smallfelem to an felem */
static void smallfelem_expand(felem out, const smallfelem in)
{
    out[0] = in[0];
    out[1] = in[1];
    out[2] = in[2];
    out[3] = in[3];
}

/*-
 * smallfelem_square sets |out| = |small|^2
 * On entry:
 *   small[i] < 2^64
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void smallfelem_square(longfelem out, const smallfelem small)
{
    limb a;
    u64 high, low;

    a = ((uint128_t) small[0]) * small[0];
    low = a;
    high = a >> 64;
    out[0] = low;
    out[1] = high;

    a = ((uint128_t) small[0]) * small[1];
    low = a;
    high = a >> 64;
    out[1] += low;
    out[1] += low;
    out[2] = high;

    a = ((uint128_t) small[0]) * small[2];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[2] *= 2;
    out[3] = high;

    a = ((uint128_t) small[0]) * small[3];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] = high;

    a = ((uint128_t) small[1]) * small[2];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[3] *= 2;
    out[4] += high;

    a = ((uint128_t) small[1]) * small[1];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[3] += high;

    a = ((uint128_t) small[1]) * small[3];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[4] *= 2;
    out[5] = high;

    a = ((uint128_t) small[2]) * small[3];
    low = a;
    high = a >> 64;
    out[5] += low;
    out[5] *= 2;
    out[6] = high;
    out[6] += high;

    a = ((uint128_t) small[2]) * small[2];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[5] += high;

    a = ((uint128_t) small[3]) * small[3];
    low = a;
    high = a >> 64;
    out[6] += low;
    out[7] = high;
}

/*-
 * felem_square sets |out| = |in|^2
 * On entry:
 *   in[i] < 2^109
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void felem_square(longfelem out, const felem in)
{
    u64 small[4];
    felem_shrink(small, in);
    smallfelem_square(out, small);
}

/*-
 * smallfelem_mul sets |out| = |small1| * |small2|
 * On entry:
 *   small1[i] < 2^64
 *   small2[i] < 2^64
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void smallfelem_mul(longfelem out, const smallfelem small1,
                           const smallfelem small2)
{
    limb a;
    u64 high, low;

    a = ((uint128_t) small1[0]) * small2[0];
    low = a;
    high = a >> 64;
    out[0] = low;
    out[1] = high;

    a = ((uint128_t) small1[0]) * small2[1];
    low = a;
    high = a >> 64;
    out[1] += low;
    out[2] = high;

    a = ((uint128_t) small1[1]) * small2[0];
    low = a;
    high = a >> 64;
    out[1] += low;
    out[2] += high;

    a = ((uint128_t) small1[0]) * small2[2];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[3] = high;

    a = ((uint128_t) small1[1]) * small2[1];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[3] += high;

    a = ((uint128_t) small1[2]) * small2[0];
    low = a;
    high = a >> 64;
    out[2] += low;
    out[3] += high;

    a = ((uint128_t) small1[0]) * small2[3];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] = high;

    a = ((uint128_t) small1[1]) * small2[2];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] += high;

    a = ((uint128_t) small1[2]) * small2[1];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] += high;

    a = ((uint128_t) small1[3]) * small2[0];
    low = a;
    high = a >> 64;
    out[3] += low;
    out[4] += high;

    a = ((uint128_t) small1[1]) * small2[3];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[5] = high;

    a = ((uint128_t) small1[2]) * small2[2];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[5] += high;

    a = ((uint128_t) small1[3]) * small2[1];
    low = a;
    high = a >> 64;
    out[4] += low;
    out[5] += high;

    a = ((uint128_t) small1[2]) * small2[3];
    low = a;
    high = a >> 64;
    out[5] += low;
    out[6] = high;

    a = ((uint128_t) small1[3]) * small2[2];
    low = a;
    high = a >> 64;
    out[5] += low;
    out[6] += high;

    a = ((uint128_t) small1[3]) * small2[3];
    low = a;
    high = a >> 64;
    out[6] += low;
    out[7] = high;
}

/*-
 * felem_mul sets |out| = |in1| * |in2|
 * On entry:
 *   in1[i] < 2^109
 *   in2[i] < 2^109
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void felem_mul(longfelem out, const felem in1, const felem in2)
{
    smallfelem small1, small2;
    felem_shrink(small1, in1);
    felem_shrink(small2, in2);
    smallfelem_mul(out, small1, small2);
}

/*-
 * felem_small_mul sets |out| = |small1| * |in2|
 * On entry:
 *   small1[i] < 2^64
 *   in2[i] < 2^109
 * On exit:
 *   out[i] < 7 * 2^64 < 2^67
 */
static void felem_small_mul(longfelem out, const smallfelem small1,
                            const felem in2)
{
    smallfelem small2;
    felem_shrink(small2, in2);
    smallfelem_mul(out, small1, small2);
}

# define two100m36m4 (((limb)1) << 100) - (((limb)1) << 36) - (((limb)1) << 4)
# define two100 (((limb)1) << 100)
# define two100m36p4 (((limb)1) << 100) - (((limb)1) << 36) + (((limb)1) << 4)
/* zero100 is 0 mod p */
static const felem zero100 =
    { two100m36m4, two100, two100m36p4, two100m36p4 };

/*-
 * Internal function for the different flavours of felem_reduce.
 * felem_reduce_ reduces the higher coefficients in[4]-in[7].
 * On entry:
 *   out[0] >= in[6] + 2^32*in[6] + in[7] + 2^32*in[7]
 *   out[1] >= in[7] + 2^32*in[4]
 *   out[2] >= in[5] + 2^32*in[5]
 *   out[3] >= in[4] + 2^32*in[5] + 2^32*in[6]
 * On exit:
 *   out[0] <= out[0] + in[4] + 2^32*in[5]
 *   out[1] <= out[1] + in[5] + 2^33*in[6]
 *   out[2] <= out[2] + in[7] + 2*in[6] + 2^33*in[7]
 *   out[3] <= out[3] + 2^32*in[4] + 3*in[7]
 */
static void felem_reduce_(felem out, const longfelem in)
{
    int128_t c;
    /* combine common terms from below */
    c = in[4] + (in[5] << 32);
    out[0] += c;
    out[3] -= c;

    c = in[5] - in[7];
    out[1] += c;
    out[2] -= c;

    /* the remaining terms */
    /* 256: [(0,1),(96,-1),(192,-1),(224,1)] */
    out[1] -= (in[4] << 32);
    out[3] += (in[4] << 32);

    /* 320: [(32,1),(64,1),(128,-1),(160,-1),(224,-1)] */
    out[2] -= (in[5] << 32);

    /* 384: [(0,-1),(32,-1),(96,2),(128,2),(224,-1)] */
    out[0] -= in[6];
    out[0] -= (in[6] << 32);
    out[1] += (in[6] << 33);
    out[2] += (in[6] * 2);
    out[3] -= (in[6] << 32);

    /* 448: [(0,-1),(32,-1),(64,-1),(128,1),(160,2),(192,3)] */
    out[0] -= in[7];
    out[0] -= (in[7] << 32);
    out[2] += (in[7] << 33);
    out[3] += (in[7] * 3);
}

/*-
 * felem_reduce converts a longfelem into an felem.
 * To be called directly after felem_square or felem_mul.
 * On entry:
 *   in[0] < 2^64, in[1] < 3*2^64, in[2] < 5*2^64, in[3] < 7*2^64
 *   in[4] < 7*2^64, in[5] < 5*2^64, in[6] < 3*2^64, in[7] < 2*64
 * On exit:
 *   out[i] < 2^101
 */
static void felem_reduce(felem out, const longfelem in)
{
    out[0] = zero100[0] + in[0];
    out[1] = zero100[1] + in[1];
    out[2] = zero100[2] + in[2];
    out[3] = zero100[3] + in[3];

    felem_reduce_(out, in);

    /*-
     * out[0] > 2^100 - 2^36 - 2^4 - 3*2^64 - 3*2^96 - 2^64 - 2^96 > 0
     * out[1] > 2^100 - 2^64 - 7*2^96 > 0
     * out[2] > 2^100 - 2^36 + 2^4 - 5*2^64 - 5*2^96 > 0
     * out[3] > 2^100 - 2^36 + 2^4 - 7*2^64 - 5*2^96 - 3*2^96 > 0
     *
     * out[0] < 2^100 + 2^64 + 7*2^64 + 5*2^96 < 2^101
     * out[1] < 2^100 + 3*2^64 + 5*2^64 + 3*2^97 < 2^101
     * out[2] < 2^100 + 5*2^64 + 2^64 + 3*2^65 + 2^97 < 2^101
     * out[3] < 2^100 + 7*2^64 + 7*2^96 + 3*2^64 < 2^101
     */
}

/*-
 * felem_reduce_zero105 converts a larger longfelem into an felem.
 * On entry:
 *   in[0] < 2^71
 * On exit:
 *   out[i] < 2^106
 */
static void felem_reduce_zero105(felem out, const longfelem in)
{
    out[0] = zero105[0] + in[0];
    out[1] = zero105[1] + in[1];
    out[2] = zero105[2] + in[2];
    out[3] = zero105[3] + in[3];

    felem_reduce_(out, in);

    /*-
     * out[0] > 2^105 - 2^41 - 2^9 - 2^71 - 2^103 - 2^71 - 2^103 > 0
     * out[1] > 2^105 - 2^71 - 2^103 > 0
     * out[2] > 2^105 - 2^41 + 2^9 - 2^71 - 2^103 > 0
     * out[3] > 2^105 - 2^41 + 2^9 - 2^71 - 2^103 - 2^103 > 0
     *
     * out[0] < 2^105 + 2^71 + 2^71 + 2^103 < 2^106
     * out[1] < 2^105 + 2^71 + 2^71 + 2^103 < 2^106
     * out[2] < 2^105 + 2^71 + 2^71 + 2^71 + 2^103 < 2^106
     * out[3] < 2^105 + 2^71 + 2^103 + 2^71 < 2^106
     */
}

/*
 * subtract_u64 sets *result = *result - v and *carry to one if the
 * subtraction underflowed.
 */
static void subtract_u64(u64 *result, u64 *carry, u64 v)
{
    uint128_t r = *result;
    r -= v;
    *carry = (r >> 64) & 1;
    *result = (u64)r;
}

/*
 * felem_contract converts |in| to its unique, minimal representation. On
 * entry: in[i] < 2^109
 */
static void felem_contract(smallfelem out, const felem in)
{
    unsigned i;
    u64 all_equal_so_far = 0, result = 0, carry;

    felem_shrink(out, in);
    /* small is minimal except that the value might be > p */

    all_equal_so_far--;
    /*
     * We are doing a constant time test if out >= kPrime. We need to compare
     * each u64, from most-significant to least significant. For each one, if
     * all words so far have been equal (m is all ones) then a non-equal
     * result is the answer. Otherwise we continue.
     */
    for (i = 3; i < 4; i--) {
        u64 equal;
        uint128_t a = ((uint128_t) kPrime[i]) - out[i];
        /*
         * if out[i] > kPrime[i] then a will underflow and the high 64-bits
         * will all be set.
         */
        result |= all_equal_so_far & ((u64)(a >> 64));

        /*
         * if kPrime[i] == out[i] then |equal| will be all zeros and the
         * decrement will make it all ones.
         */
        equal = kPrime[i] ^ out[i];
        equal--;
        equal &= equal << 32;
        equal &= equal << 16;
        equal &= equal << 8;
        equal &= equal << 4;
        equal &= equal << 2;
        equal &= equal << 1;
        equal = ((s64) equal) >> 63;

        all_equal_so_far &= equal;
    }

    /*
     * if all_equal_so_far is still all ones then the two values are equal
     * and so out >= kPrime is true.
     */
    result |= all_equal_so_far;

    /* if out >= kPrime then we subtract kPrime. */
    subtract_u64(&out[0], &carry, result & kPrime[0]);
    subtract_u64(&out[1], &carry, carry);
    subtract_u64(&out[2], &carry, carry);
    subtract_u64(&out[3], &carry, carry);

    subtract_u64(&out[1], &carry, result & kPrime[1]);
    subtract_u64(&out[2], &carry, carry);
    subtract_u64(&out[3], &carry, carry);

    subtract_u64(&out[2], &carry, result & kPrime[2]);
    subtract_u64(&out[3], &carry, carry);

    subtract_u64(&out[3], &carry, result & kPrime[3]);
}

static void smallfelem_square_contract(smallfelem out, const smallfelem in)
{
    longfelem longtmp;
    felem tmp;

    smallfelem_square(longtmp, in);
    felem_reduce(tmp, longtmp);
    felem_contract(out, tmp);
}

static void smallfelem_mul_contract(smallfelem out, const smallfelem in1,
                                    const smallfelem in2)
{
    longfelem longtmp;
    felem tmp;

    smallfelem_mul(longtmp, in1, in2);
    felem_reduce(tmp, longtmp);
    felem_contract(out, tmp);
}

/*-
 * felem_is_zero returns a limb with all bits set if |in| == 0 (mod p) and 0
 * otherwise.
 * On entry:
 *   small[i] < 2^64
 */
static limb smallfelem_is_zero(const smallfelem small)
{
    limb result;
    u64 is_p;

    u64 is_zero = small[0] | small[1] | small[2] | small[3];
    is_zero--;
    is_zero &= is_zero << 32;
    is_zero &= is_zero << 16;
    is_zero &= is_zero << 8;
    is_zero &= is_zero << 4;
    is_zero &= is_zero << 2;
    is_zero &= is_zero << 1;
    is_zero = ((s64) is_zero) >> 63;

    is_p = (small[0] ^ kPrime[0]) |
        (small[1] ^ kPrime[1]) |
        (small[2] ^ kPrime[2]) | (small[3] ^ kPrime[3]);
    is_p--;
    is_p &= is_p << 32;
    is_p &= is_p << 16;
    is_p &= is_p << 8;
    is_p &= is_p << 4;
    is_p &= is_p << 2;
    is_p &= is_p << 1;
    is_p = ((s64) is_p) >> 63;

    is_zero |= is_p;

    result = is_zero;
    result |= ((limb) is_zero) << 64;
    return result;
}

static int smallfelem_is_zero_int(const smallfelem small)
{
    return (int)(smallfelem_is_zero(small) & ((limb) 1));
}

/*-
 * felem_inv calculates |out| = |in|^{-1}
 *
 * Based on Fermat's Little Theorem:
 *   a^p = a (mod p)
 *   a^{p-1} = 1 (mod p)
 *   a^{p-2} = a^{-1} (mod p)
 */
static void felem_inv(felem out, const felem in)
{
    felem ftmp, ftmp2;
    /* each e_I will hold |in|^{2^I - 1} */
    felem e2, e4, e8, e16, e32, e64;
    longfelem tmp;
    unsigned i;

    felem_square(tmp, in);
    felem_reduce(ftmp, tmp);    /* 2^1 */
    felem_mul(tmp, in, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^2 - 2^0 */
    felem_assign(e2, ftmp);
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^3 - 2^1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^4 - 2^2 */
    felem_mul(tmp, ftmp, e2);
    felem_reduce(ftmp, tmp);    /* 2^4 - 2^0 */
    felem_assign(e4, ftmp);
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^5 - 2^1 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^6 - 2^2 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^7 - 2^3 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);    /* 2^8 - 2^4 */
    felem_mul(tmp, ftmp, e4);
    felem_reduce(ftmp, tmp);    /* 2^8 - 2^0 */
    felem_assign(e8, ftmp);
    for (i = 0; i < 8; i++) {
        felem_square(tmp, ftmp);
        felem_reduce(ftmp, tmp);
    }                           /* 2^16 - 2^8 */
    felem_mul(tmp, ftmp, e8);
    felem_reduce(ftmp, tmp);    /* 2^16 - 2^0 */
    felem_assign(e16, ftmp);
    for (i = 0; i < 16; i++) {
        felem_square(tmp, ftmp);
        felem_reduce(ftmp, tmp);
    }                           /* 2^32 - 2^16 */
    felem_mul(tmp, ftmp, e16);
    felem_reduce(ftmp, tmp);    /* 2^32 - 2^0 */
    felem_assign(e32, ftmp);
    for (i = 0; i < 32; i++) {
        felem_square(tmp, ftmp);
        felem_reduce(ftmp, tmp);
    }                           /* 2^64 - 2^32 */
    felem_assign(e64, ftmp);
    felem_mul(tmp, ftmp, in);
    felem_reduce(ftmp, tmp);    /* 2^64 - 2^32 + 2^0 */
    for (i = 0; i < 192; i++) {
        felem_square(tmp, ftmp);
        felem_reduce(ftmp, tmp);
    }                           /* 2^256 - 2^224 + 2^192 */

    felem_mul(tmp, e64, e32);
    felem_reduce(ftmp2, tmp);   /* 2^64 - 2^0 */
    for (i = 0; i < 16; i++) {
        felem_square(tmp, ftmp2);
        felem_reduce(ftmp2, tmp);
    }                           /* 2^80 - 2^16 */
    felem_mul(tmp, ftmp2, e16);
    felem_reduce(ftmp2, tmp);   /* 2^80 - 2^0 */
    for (i = 0; i < 8; i++) {
        felem_square(tmp, ftmp2);
        felem_reduce(ftmp2, tmp);
    }                           /* 2^88 - 2^8 */
    felem_mul(tmp, ftmp2, e8);
    felem_reduce(ftmp2, tmp);   /* 2^88 - 2^0 */
    for (i = 0; i < 4; i++) {
        felem_square(tmp, ftmp2);
        felem_reduce(ftmp2, tmp);
    }                           /* 2^92 - 2^4 */
    felem_mul(tmp, ftmp2, e4);
    felem_reduce(ftmp2, tmp);   /* 2^92 - 2^0 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^93 - 2^1 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^94 - 2^2 */
    felem_mul(tmp, ftmp2, e2);
    felem_reduce(ftmp2, tmp);   /* 2^94 - 2^0 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^95 - 2^1 */
    felem_square(tmp, ftmp2);
    felem_reduce(ftmp2, tmp);   /* 2^96 - 2^2 */
    felem_mul(tmp, ftmp2, in);
    felem_reduce(ftmp2, tmp);   /* 2^96 - 3 */

    felem_mul(tmp, ftmp2, ftmp);
    felem_reduce(out, tmp);     /* 2^256 - 2^224 + 2^192 + 2^96 - 3 */
}

static void smallfelem_inv_contract(smallfelem out, const smallfelem in)
{
    felem tmp;

    smallfelem_expand(tmp, in);
    felem_inv(tmp, tmp);
    felem_contract(out, tmp);
}

/*-
 * Group operations
 * ----------------
 *
 * Building on top of the field operations we have the operations on the
 * elliptic curve group itself. Points on the curve are represented in Jacobian
 * coordinates
 */

/*-
 * point_double calculates 2*(x_in, y_in, z_in)
 *
 * The method is taken from:
 *   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
 *
 * Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed.
 * while x_out == y_in is not (maybe this works, but it's not tested).
 */
static void
point_double(felem x_out, felem y_out, felem z_out,
             const felem x_in, const felem y_in, const felem z_in)
{
    longfelem tmp, tmp2;
    felem delta, gamma, beta, alpha, ftmp, ftmp2;
    smallfelem small1, small2;

    felem_assign(ftmp, x_in);
    /* ftmp[i] < 2^106 */
    felem_assign(ftmp2, x_in);
    /* ftmp2[i] < 2^106 */

    /* delta = z^2 */
    felem_square(tmp, z_in);
    felem_reduce(delta, tmp);
    /* delta[i] < 2^101 */

    /* gamma = y^2 */
    felem_square(tmp, y_in);
    felem_reduce(gamma, tmp);
    /* gamma[i] < 2^101 */
    felem_shrink(small1, gamma);

    /* beta = x*gamma */
    felem_small_mul(tmp, small1, x_in);
    felem_reduce(beta, tmp);
    /* beta[i] < 2^101 */

    /* alpha = 3*(x-delta)*(x+delta) */
    felem_diff(ftmp, delta);
    /* ftmp[i] < 2^105 + 2^106 < 2^107 */
    felem_sum(ftmp2, delta);
    /* ftmp2[i] < 2^105 + 2^106 < 2^107 */
    felem_scalar(ftmp2, 3);
    /* ftmp2[i] < 3 * 2^107 < 2^109 */
    felem_mul(tmp, ftmp, ftmp2);
    felem_reduce(alpha, tmp);
    /* alpha[i] < 2^101 */
    felem_shrink(small2, alpha);

    /* x' = alpha^2 - 8*beta */
    smallfelem_square(tmp, small2);
    felem_reduce(x_out, tmp);
    felem_assign(ftmp, beta);
    felem_scalar(ftmp, 8);
    /* ftmp[i] < 8 * 2^101 = 2^104 */
    felem_diff(x_out, ftmp);
    /* x_out[i] < 2^105 + 2^101 < 2^106 */

    /* z' = (y + z)^2 - gamma - delta */
    felem_sum(delta, gamma);
    /* delta[i] < 2^101 + 2^101 = 2^102 */
    felem_assign(ftmp, y_in);
    felem_sum(ftmp, z_in);
    /* ftmp[i] < 2^106 + 2^106 = 2^107 */
    felem_square(tmp, ftmp);
    felem_reduce(z_out, tmp);
    felem_diff(z_out, delta);
    /* z_out[i] < 2^105 + 2^101 < 2^106 */

    /* y' = alpha*(4*beta - x') - 8*gamma^2 */
    felem_scalar(beta, 4);
    /* beta[i] < 4 * 2^101 = 2^103 */
    felem_diff_zero107(beta, x_out);
    /* beta[i] < 2^107 + 2^103 < 2^108 */
    felem_small_mul(tmp, small2, beta);
    /* tmp[i] < 7 * 2^64 < 2^67 */
    smallfelem_square(tmp2, small1);
    /* tmp2[i] < 7 * 2^64 */
    longfelem_scalar(tmp2, 8);
    /* tmp2[i] < 8 * 7 * 2^64 = 7 * 2^67 */
    longfelem_diff(tmp, tmp2);
    /* tmp[i] < 2^67 + 2^70 + 2^40 < 2^71 */
    felem_reduce_zero105(y_out, tmp);
    /* y_out[i] < 2^106 */
}

/*
 * point_double_small is the same as point_double, except that it operates on
 * smallfelems
 */
static void
point_double_small(smallfelem x_out, smallfelem y_out, smallfelem z_out,
                   const smallfelem x_in, const smallfelem y_in,
                   const smallfelem z_in)
{
    felem felem_x_out, felem_y_out, felem_z_out;
    felem felem_x_in, felem_y_in, felem_z_in;

    smallfelem_expand(felem_x_in, x_in);
    smallfelem_expand(felem_y_in, y_in);
    smallfelem_expand(felem_z_in, z_in);
    point_double(felem_x_out, felem_y_out, felem_z_out,
                 felem_x_in, felem_y_in, felem_z_in);
    felem_shrink(x_out, felem_x_out);
    felem_shrink(y_out, felem_y_out);
    felem_shrink(z_out, felem_z_out);
}

/* copy_conditional copies in to out iff mask is all ones. */
static void copy_conditional(felem out, const felem in, limb mask)
{
    unsigned i;
    for (i = 0; i < NLIMBS; ++i) {
        const limb tmp = mask & (in[i] ^ out[i]);
        out[i] ^= tmp;
    }
}

/* copy_small_conditional copies in to out iff mask is all ones. */
static void copy_small_conditional(felem out, const smallfelem in, limb mask)
{
    unsigned i;
    const u64 mask64 = mask;
    for (i = 0; i < NLIMBS; ++i) {
        out[i] = ((limb) (in[i] & mask64)) | (out[i] & ~mask);
    }
}

/*-
 * point_add calculates (x1, y1, z1) + (x2, y2, z2)
 *
 * The method is taken from:
 *   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#addition-add-2007-bl,
 * adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
 *
 * This function includes a branch for checking whether the two input points
 * are equal, (while not equal to the point at infinity). This case never
 * happens during single point multiplication, so there is no timing leak for
 * ECDH or ECDSA signing.
 */
void point_add(felem x3, felem y3, felem z3,
                      const felem x1, const felem y1, const felem z1,
                      const int mixed, const smallfelem x2,
                      const smallfelem y2, const smallfelem z2)
{
    felem ftmp, ftmp2, ftmp3, ftmp4, ftmp5, ftmp6, x_out, y_out, z_out;
    longfelem tmp, tmp2;
    smallfelem small1, small2, small3, small4, small5;
    limb x_equal, y_equal, z1_is_zero, z2_is_zero;

    felem_shrink(small3, z1);

    z1_is_zero = smallfelem_is_zero(small3);
    z2_is_zero = smallfelem_is_zero(z2);

    /* ftmp = z1z1 = z1**2 */
    smallfelem_square(tmp, small3);
    felem_reduce(ftmp, tmp);
    /* ftmp[i] < 2^101 */
    felem_shrink(small1, ftmp);

    if (!mixed) {
        /* ftmp2 = z2z2 = z2**2 */
        smallfelem_square(tmp, z2);
        felem_reduce(ftmp2, tmp);
        /* ftmp2[i] < 2^101 */
        felem_shrink(small2, ftmp2);

        felem_shrink(small5, x1);

        /* u1 = ftmp3 = x1*z2z2 */
        smallfelem_mul(tmp, small5, small2);
        felem_reduce(ftmp3, tmp);
        /* ftmp3[i] < 2^101 */

        /* ftmp5 = z1 + z2 */
        felem_assign(ftmp5, z1);
        felem_small_sum(ftmp5, z2);
        /* ftmp5[i] < 2^107 */

        /* ftmp5 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2 */
        felem_square(tmp, ftmp5);
        felem_reduce(ftmp5, tmp);
        /* ftmp2 = z2z2 + z1z1 */
        felem_sum(ftmp2, ftmp);
        /* ftmp2[i] < 2^101 + 2^101 = 2^102 */
        felem_diff(ftmp5, ftmp2);
        /* ftmp5[i] < 2^105 + 2^101 < 2^106 */

        /* ftmp2 = z2 * z2z2 */
        smallfelem_mul(tmp, small2, z2);
        felem_reduce(ftmp2, tmp);

        /* s1 = ftmp2 = y1 * z2**3 */
        felem_mul(tmp, y1, ftmp2);
        felem_reduce(ftmp6, tmp);
        /* ftmp6[i] < 2^101 */
    } else {
        /*
         * We'll assume z2 = 1 (special case z2 = 0 is handled later)
         */

        /* u1 = ftmp3 = x1*z2z2 */
        felem_assign(ftmp3, x1);
        /* ftmp3[i] < 2^106 */

        /* ftmp5 = 2z1z2 */
        felem_assign(ftmp5, z1);
        felem_scalar(ftmp5, 2);
        /* ftmp5[i] < 2*2^106 = 2^107 */

        /* s1 = ftmp2 = y1 * z2**3 */
        felem_assign(ftmp6, y1);
        /* ftmp6[i] < 2^106 */
    }

    /* u2 = x2*z1z1 */
    smallfelem_mul(tmp, x2, small1);
    felem_reduce(ftmp4, tmp);

    /* h = ftmp4 = u2 - u1 */
    felem_diff_zero107(ftmp4, ftmp3);
    /* ftmp4[i] < 2^107 + 2^101 < 2^108 */
    felem_shrink(small4, ftmp4);

    x_equal = smallfelem_is_zero(small4);

    /* z_out = ftmp5 * h */
    felem_small_mul(tmp, small4, ftmp5);
    felem_reduce(z_out, tmp);
    /* z_out[i] < 2^101 */

    /* ftmp = z1 * z1z1 */
    smallfelem_mul(tmp, small1, small3);
    felem_reduce(ftmp, tmp);

    /* s2 = tmp = y2 * z1**3 */
    felem_small_mul(tmp, y2, ftmp);
    felem_reduce(ftmp5, tmp);

    /* r = ftmp5 = (s2 - s1)*2 */
    felem_diff_zero107(ftmp5, ftmp6);
    /* ftmp5[i] < 2^107 + 2^107 = 2^108 */
    felem_scalar(ftmp5, 2);
    /* ftmp5[i] < 2^109 */
    felem_shrink(small1, ftmp5);
    y_equal = smallfelem_is_zero(small1);

    if (x_equal && y_equal && !z1_is_zero && !z2_is_zero) {
        point_double(x3, y3, z3, x1, y1, z1);
        return;
    }

    /* I = ftmp = (2h)**2 */
    felem_assign(ftmp, ftmp4);
    felem_scalar(ftmp, 2);
    /* ftmp[i] < 2*2^108 = 2^109 */
    felem_square(tmp, ftmp);
    felem_reduce(ftmp, tmp);

    /* J = ftmp2 = h * I */
    felem_mul(tmp, ftmp4, ftmp);
    felem_reduce(ftmp2, tmp);

    /* V = ftmp4 = U1 * I */
    felem_mul(tmp, ftmp3, ftmp);
    felem_reduce(ftmp4, tmp);

    /* x_out = r**2 - J - 2V */
    smallfelem_square(tmp, small1);
    felem_reduce(x_out, tmp);
    felem_assign(ftmp3, ftmp4);
    felem_scalar(ftmp4, 2);
    felem_sum(ftmp4, ftmp2);
    /* ftmp4[i] < 2*2^101 + 2^101 < 2^103 */
    felem_diff(x_out, ftmp4);
    /* x_out[i] < 2^105 + 2^101 */

    /* y_out = r(V-x_out) - 2 * s1 * J */
    felem_diff_zero107(ftmp3, x_out);
    /* ftmp3[i] < 2^107 + 2^101 < 2^108 */
    felem_small_mul(tmp, small1, ftmp3);
    felem_mul(tmp2, ftmp6, ftmp2);
    longfelem_scalar(tmp2, 2);
    /* tmp2[i] < 2*2^67 = 2^68 */
    longfelem_diff(tmp, tmp2);
    /* tmp[i] < 2^67 + 2^70 + 2^40 < 2^71 */
    felem_reduce_zero105(y_out, tmp);
    /* y_out[i] < 2^106 */

    copy_small_conditional(x_out, x2, z1_is_zero);
    copy_conditional(x_out, x1, z2_is_zero);
    copy_small_conditional(y_out, y2, z1_is_zero);
    copy_conditional(y_out, y1, z2_is_zero);
    copy_small_conditional(z_out, z2, z1_is_zero);
    copy_conditional(z_out, z1, z2_is_zero);
    felem_assign(x3, x_out);
    felem_assign(y3, y_out);
    felem_assign(z3, z_out);
}
