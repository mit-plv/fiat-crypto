#include "inversion.c"
#include <string.h>
#include <time.h>

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
      /* printf("[%i]",a[i]); */
    }

    fiat_test_from_bytes(g1,a);
    fiat_test_from_bytes(g2,a);
    fiat_test_from_montgomery(g3,g2);

    for (int i = 0; i < LIMBS; i++) g[i] = g3[i];
    g[SAT_LIMBS - 1] = 0;

    inverse(out,g);

    fiat_test_mul(res,out,g1);
    fiat_test_from_montgomery(out,res);
    fiat_test_to_bytes(a,out);

    /* printf("\n [%i]",a[0]); */
    if (a[0] != 1) {
      printf("FAIL\n");
      return 2;
    }
    for (i = 1; i < BYTES; i++) {
      if (a[i] != 0) {
        printf("FAIL\n");
        return 1;
        /* printf("[%i]",a[i]); */
      }
    }
  }
  printf("PASS\n");
  return 0;
}
