static void fesquare(uint64_t out[4], const uint64_t in1[4]) {
  { const uint64_t x5 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint128_t x7 = (((uint128_t)x2 * x5) + (((uint128_t)x4 * x6) + (((uint128_t)x6 * x4) + ((uint128_t)x5 * x2))));
  { uint128_t x8 = ((((uint128_t)x2 * x6) + (((uint128_t)x4 * x4) + ((uint128_t)x6 * x2))) + (0x1b * ((uint128_t)x5 * x5)));
  { uint128_t x9 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) + (0x1b * (((uint128_t)x6 * x5) + ((uint128_t)x5 * x6))));
  { uint128_t x10 = (((uint128_t)x2 * x2) + (0x1b * (((uint128_t)x4 * x5) + (((uint128_t)x6 * x6) + ((uint128_t)x5 * x4)))));
  { uint64_t x11 = (uint64_t) (x10 >> 0x23);
  { uint64_t x12 = ((uint64_t)x10 & 0x7ffffffff);
  { uint128_t x13 = (x11 + x9);
  { uint64_t x14 = (uint64_t) (x13 >> 0x23);
  { uint64_t x15 = ((uint64_t)x13 & 0x7ffffffff);
  { uint128_t x16 = (x14 + x8);
  { uint64_t x17 = (uint64_t) (x16 >> 0x23);
  { uint64_t x18 = ((uint64_t)x16 & 0x7ffffffff);
  { uint128_t x19 = (x17 + x7);
  { uint64_t x20 = (uint64_t) (x19 >> 0x23);
  { uint64_t x21 = ((uint64_t)x19 & 0x7ffffffff);
  { uint64_t x22 = (x12 + (0x1b * x20));
  { uint64_t x23 = (x22 >> 0x23);
  { uint64_t x24 = (x22 & 0x7ffffffff);
  { uint64_t x25 = (x23 + x15);
  { uint64_t x26 = (x25 >> 0x23);
  { uint64_t x27 = (x25 & 0x7ffffffff);
  out[0] = x24;
  out[1] = x27;
  out[2] = (x26 + x18);
  out[3] = x21;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
