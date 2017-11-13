static void fesquare(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint128_t x9 = (((uint128_t)x2 * x7) + (((uint128_t)x4 * x8) + (((uint128_t)x6 * x6) + (((uint128_t)x8 * x4) + ((uint128_t)x7 * x2)))));
  { uint128_t x10 = ((((uint128_t)x2 * x8) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x8 * x2)))) + (0x2fd * ((uint128_t)x7 * x7)));
  { uint128_t x11 = ((((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))) + (0x2fd * (((uint128_t)x8 * x7) + ((uint128_t)x7 * x8))));
  { uint128_t x12 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x2fd * (((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6)))));
  { uint128_t x13 = (((uint128_t)x2 * x2) + (0x2fd * (((uint128_t)x4 * x7) + (((uint128_t)x6 * x8) + (((uint128_t)x8 * x6) + ((uint128_t)x7 * x4))))));
  { uint128_t x14 = (x13 >> 0x33);
  { uint64_t x15 = ((uint64_t)x13 & 0x7ffffffffffff);
  { uint128_t x16 = (x14 + x12);
  { uint128_t x17 = (x16 >> 0x33);
  { uint64_t x18 = ((uint64_t)x16 & 0x7ffffffffffff);
  { uint128_t x19 = (x17 + x11);
  { uint128_t x20 = (x19 >> 0x33);
  { uint64_t x21 = ((uint64_t)x19 & 0x7ffffffffffff);
  { uint128_t x22 = (x20 + x10);
  { uint128_t x23 = (x22 >> 0x33);
  { uint64_t x24 = ((uint64_t)x22 & 0x7ffffffffffff);
  { uint128_t x25 = (x23 + x9);
  { uint64_t x26 = (uint64_t) (x25 >> 0x33);
  { uint64_t x27 = ((uint64_t)x25 & 0x7ffffffffffff);
  { uint128_t x28 = (x15 + ((uint128_t)0x2fd * x26));
  { uint64_t x29 = (uint64_t) (x28 >> 0x33);
  { uint64_t x30 = ((uint64_t)x28 & 0x7ffffffffffff);
  { uint64_t x31 = (x29 + x18);
  { uint64_t x32 = (x31 >> 0x33);
  { uint64_t x33 = (x31 & 0x7ffffffffffff);
  out[0] = x30;
  out[1] = x33;
  out[2] = (x32 + x21);
  out[3] = x24;
  out[4] = x27;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
