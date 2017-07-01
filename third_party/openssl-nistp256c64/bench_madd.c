#include <stdint.h>
#include "ecp_nistp256.h"

void bench_madd(unsigned char* buf) {
  uint128_t* x3 = (uint128_t*) buf;
  uint128_t* y3 = (uint128_t*) (buf + 1*sizeof(felem));
  uint128_t* z3 = (uint128_t*) (buf + 2*sizeof(felem));
  uint128_t* x1 = (uint128_t*) (buf + 3*sizeof(felem));
  uint128_t* y1 = (uint128_t*) (buf + 4*sizeof(felem));
  uint128_t* z1 = (uint128_t*) (buf + 5*sizeof(felem));
  int mixed = 1;
  uint64_t* x2 = (uint64_t*) (buf + 6*sizeof(felem));
  uint64_t* y2 = (uint64_t*) (buf + 6*sizeof(felem) + sizeof(smallfelem));
  smallfelem z2 = {1, 0, 0, 0};
  point_add(x3, y3, z3, x1, y1, z1, mixed, x2, y2, z2);
}
