#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include "femul.h"

// all arrays big-endian
static uint64_t Rmodm[4] = {0xfffffffe, 0xffffffffffffffff, 0xffffffff00000000, 0x0000000000000001};

int main() {
  uint64_t out[4] = {0};
  if ( femul(out,
        Rmodm[0], Rmodm[1], Rmodm[2], Rmodm[3],
        Rmodm[0], Rmodm[1], Rmodm[2], Rmodm[3]), 
      ! (out[0]   == Rmodm[0]
        && out[1] == Rmodm[1]
        && out[2] == Rmodm[2]
        && out[3] == Rmodm[3]
        )) { return 1; }
  if ( femul(out,
        0, 0, 0, 0,
        Rmodm[0], Rmodm[1], Rmodm[2], Rmodm[3]), 
      ! (out[0]   == 0
        && out[1] == 0
        && out[2] == 0
        && out[3] == 0
        )) { return 2; }
  if ( femul(out,
        0, 0, 0, 1,
        0, 0, 0, 1), 
      ! (out[0]   == 0xfffffffe00000003 // R^-1
        && out[1] == 0xfffffffd00000002
        && out[2] == 0x00000001fffffffe
        && out[3] == 0x0000000300000000
        )) { return 3; }
  if ( femul(out,
        0, 0, 0, 1,
        0x4fffffffd, 0xfffffffffffffffe, 0xfffffffbffffffff, 0x0000000000000003),  // R^2
      ! (out[0]   == Rmodm[0]
        && out[1] == Rmodm[1]
        && out[2] == Rmodm[2]
        && out[3] == Rmodm[3]
        )) { return 4; }
  if ( femul(out,
        0, 0, 0, 0,
        2141451, Rmodm[2], -3251252, 2134), 
      ! (out[0]   == 0
        && out[1] == 0
        && out[2] == 0
        && out[3] == 0
        )) { return 5; }

  //printf("0x%016" PRIx64 " 0x%016" PRIx64 " 0x%016" PRIx64 " 0x%016" PRIx64 "\n", out[0], out[1], out[2], out[3]);
  //printf("((((((0x%016" PRIx64 "<<64)+ 0x%016" PRIx64 ")<<64)+ 0x%016" PRIx64 ")<<64)+ 0x%016" PRIx64 ")\n", out[0], out[1], out[2], out[3]);
  return 0;
}
