#include <stdint.h>
#include "nistz256.h"

void bench_madd(unsigned char* buf) {
  P256_POINT* r = (P256_POINT*) buf;
  P256_POINT_AFFINE* b = (P256_POINT_AFFINE*) (buf + sizeof(P256_POINT));
  ecp_nistz256_point_add_affine(r, r, b);
}
