static void fesquare(uint64_t out[3], const uint64_t in1[3]) {
  { const uint64_t x3 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint128_t x5 = (((uint128_t)x2 * x3) + (((uint128_t)x4 * x4) + ((uint128_t)x3 * x2)));
  { uint128_t x6 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x5 * ((uint128_t)x3 * x3)));
  { uint128_t x7 = (((uint128_t)x2 * x2) + (0x5 * (((uint128_t)x4 * x3) + ((uint128_t)x3 * x4))));
  { uint64_t x8 = (uint64_t) (x7 >> 0x32);
  { uint64_t x9 = ((uint64_t)x7 & 0x3ffffffffffff);
  { uint128_t x10 = (x8 + x6);
  { uint64_t x11 = (uint64_t) (x10 >> 0x32);
  { uint64_t x12 = ((uint64_t)x10 & 0x3ffffffffffff);
  { uint128_t x13 = (x11 + x5);
  { uint64_t x14 = (uint64_t) (x13 >> 0x32);
  { uint64_t x15 = ((uint64_t)x13 & 0x3ffffffffffff);
  { uint64_t x16 = (x9 + (0x5 * x14));
  { uint64_t x17 = (x16 >> 0x32);
  { uint64_t x18 = (x16 & 0x3ffffffffffff);
  { uint64_t x19 = (x17 + x12);
  { uint64_t x20 = (x19 >> 0x32);
  { uint64_t x21 = (x19 & 0x3ffffffffffff);
  out[0] = x18;
  out[1] = x21;
  out[2] = (x20 + x15);
  }}}}}}}}}}}}}}}}}}}}
}
