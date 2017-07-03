#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include "feadd.h"

static int check(uint64_t out[4], uint64_t ref[4]) {
  return out[0] == ref[0] && out[1] == ref[1] && out[2] == ref[2] && out[3] == ref[3];
}

int main() {
  {
    uint64_t out[4] = {0};
    uint64_t in1[4] = {0, 0, 0, 1};
    uint64_t in2[4] = {0, 0, 0, 1};
    uint64_t ref[4] = {0, 0, 0, 2};
    feadd(out, in1[0], in1[1], in1[2], in1[3], in2[0], in2[1], in2[2], in2[3]);
    if (!check(out, ref)) return 1;
  }
  {
    uint64_t out[4] = {0};
    uint64_t in1[4] = {0, 0, 0, 0};
    uint64_t in2[4] = {0, 0, 0, 0};
    uint64_t ref[4] = {0, 0, 0, 0};
    feadd(out, in1[0], in1[1], in1[2], in1[3], in2[0], in2[1], in2[2], in2[3]);
    if (!check(out, ref)) return 2;
  }
  {
    uint64_t out[4] = {0};
    uint64_t in1[4] = {0xffffffff00000001, 0x0000000000000000, 0x00000000ffffffff, 0xfffffffffffffffe}; // p256-1
    uint64_t in2[4] = {0, 0, 0, 1};
    uint64_t ref[4] = {0, 0, 0, 0};
    feadd(out, in1[0], in1[1], in1[2], in1[3], in2[0], in2[1], in2[2], in2[3]);
    if (!check(out, ref)) return 3;
  }
  {
    uint64_t out[4] = {0};
    uint64_t in1[4] = {0xffffffff00000001, 0x0000000000000000, 0x00000000ffffffff, 0xfffffffffffffffe}; // p256-1
    uint64_t in2[4] = {0, 0, 0, 7};
    uint64_t ref[4] = {0, 0, 0, 6};
    feadd(out, in1[0], in1[1], in1[2], in1[3], in2[0], in2[1], in2[2], in2[3]);
    if (!check(out, ref)) return 4;
  }
  
  //printf("0x%016" PRIx64 " 0x%016" PRIx64 " 0x%016" PRIx64 " 0x%016" PRIx64 "\n", out[0], out[1], out[2], out[3]);
  //printf("((((((0x%016" PRIx64 "<<64)+ 0x%016" PRIx64 ")<<64)+ 0x%016" PRIx64 ")<<64)+ 0x%016" PRIx64 ")\n", out[0], out[1], out[2], out[3]);
}
