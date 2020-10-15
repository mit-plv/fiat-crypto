#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAKE_FN_NAME1(x,y) x ## y
#define MAKE_FN_NAME(x,y) MAKE_FN_NAME1(x,y)

#define FROM_BYTES MAKE_FN_NAME(CURVE_DESCRIPTION,_from_bytes)
#define TO_BYTES MAKE_FN_NAME(CURVE_DESCRIPTION,_to_bytes)
#define FROM_MONTGOMERY MAKE_FN_NAME(CURVE_DESCRIPTION,_from_montgomery)

int main() {
  WORD res[LIMBS], out[LIMBS], g[SAT_LIMBS], g1[LIMBS], g2[LIMBS], g3[LIMBS];
  uint8_t a[BYTES];

  int seed = time(0);
  srand(seed);
  printf("%i\n", seed);

  for (int j = 0; j < 1000; j++) {
    int i;
    for (i = 0; i < BYTES; i++) {
      a[i] = rand() % 256;
      if (i > BYTES - 8) a[i] = 0;
    }

    FROM_BYTES(g1,a);
    FROM_BYTES(g2,a);
    FROM_MONTGOMERY(g3,g2);

    for (int i = 0; i < LIMBS; i++) g[i] = g3[i];
    g[SAT_LIMBS - 1] = 0;

    inverse(out,g);

    MUL(res,out,g1);
    FROM_MONTGOMERY(out,res);
    TO_BYTES(a,out);

    if (a[0] != 1) {
      printf("FAIL\n");
      return 2;
    }
    for (i = 1; i < BYTES; i++) {
      if (a[i] != 0) {
        printf("FAIL\n");
        return 1;
      }
    }
  }
  printf("PASS\n");
  return 0;
}
