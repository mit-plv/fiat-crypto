#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <inttypes.h>
#include "montgomery_inversion.c"

/* CHANGE THESE ACCORDING TO PRIME AND WORDSIZE */
#define LIMBS 8 /* amount of limbs pr. large integer in montgomery domain, see montgomery_inversion */
#define WORD uint32_t
#define WORDSIZE 32 /* wordsize */
#define LEN_PRIME 256 /* length of the prime in bits */
/* DON'T CHANGE ANYTHING BELOW HERE */

#if LEN_PRIME < 46
#define ITERATIONS (((49 * LEN_PRIME) + 80) / 17)
#else
#define ITERATIONS (((49 * LEN_PRIME) + 57) / 17)
#endif

#define SAT_LIMBS LIMBS + 1 /* we might need 2 more bits to represent m in twos complement */
#define BYTES 8 * (((LEN_PRIME - 1) / 64) + 1)

void inverse(WORD out[LIMBS], WORD g[SAT_LIMBS]) {

  WORD precomp[LIMBS];
  fiat_test_precomp(precomp);

  WORD d = 1;
  WORD f[SAT_LIMBS];
  WORD v[LIMBS];
  WORD r[LIMBS];
  WORD out1;
  WORD out2[SAT_LIMBS], out3[SAT_LIMBS], out4[LIMBS], out5[LIMBS];

  fiat_test_msat(f);
  fiat_test_one(r);
  for (int j = 0; j < LIMBS; j++) v[j] = 0;

  for (int i = 0; i < ITERATIONS - (ITERATIONS % 2); i+=2) {
    fiat_test_divstep(&out1,out2,out3,out4,out5,d,f,g,v,r);
    fiat_test_divstep(&d,f,g,v,r,out1,out2,out3,out4,out5);
  }
  if (ITERATIONS % 2) {
    fiat_test_divstep(&out1,out2,out3,out4,out5,d,f,g,v,r);
    for (int k = 0; k < LIMBS; k++) v[k] = out4[k];
    for (int k = 0; k < SAT_LIMBS; k++) f[k] = out2[k];
  }

  WORD h[LIMBS];
  if (f[SAT_LIMBS - 1] >> (WORDSIZE - 1)) {
    fiat_test_opp(h, v);
    for (int k = 0; k < LIMBS; k++) v[k] = h[k];
  }

  fiat_test_mul(out, v, precomp);

  return;
}
