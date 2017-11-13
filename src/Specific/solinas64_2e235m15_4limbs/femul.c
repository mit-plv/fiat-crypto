static void femul(uint64_t out[4], const uint64_t in1[4], const uint64_t in2[4]) {
  { const uint64_t x8 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x14 = in2[3];
  { const uint64_t x15 = in2[2];
  { const uint64_t x13 = in2[1];
  { const uint64_t x11 = in2[0];
  { uint128_t x16 = (((uint128_t)x5 * x14) + (((uint128_t)x7 * x15) + (((uint128_t)x9 * x13) + ((uint128_t)x8 * x11))));
  { uint128_t x17 = ((((uint128_t)x5 * x15) + (((uint128_t)x7 * x13) + ((uint128_t)x9 * x11))) + (0xf * (0x2 * ((uint128_t)x8 * x14))));
  { uint128_t x18 = ((((uint128_t)x5 * x13) + ((uint128_t)x7 * x11)) + (0xf * ((0x2 * ((uint128_t)x9 * x14)) + (0x2 * ((uint128_t)x8 * x15)))));
  { uint128_t x19 = (((uint128_t)x5 * x11) + (0xf * ((0x2 * ((uint128_t)x7 * x14)) + ((0x2 * ((uint128_t)x9 * x15)) + (0x2 * ((uint128_t)x8 * x13))))));
  { uint128_t x20 = (x19 >> 0x3b);
  { uint64_t x21 = ((uint64_t)x19 & 0x7ffffffffffffff);
  { uint128_t x22 = (x20 + x18);
  { uint128_t x23 = (x22 >> 0x3b);
  { uint64_t x24 = ((uint64_t)x22 & 0x7ffffffffffffff);
  { uint128_t x25 = (x23 + x17);
  { uint128_t x26 = (x25 >> 0x3b);
  { uint64_t x27 = ((uint64_t)x25 & 0x7ffffffffffffff);
  { uint128_t x28 = (x26 + x16);
  { uint128_t x29 = (x28 >> 0x3a);
  { uint64_t x30 = ((uint64_t)x28 & 0x3ffffffffffffff);
  { uint128_t x31 = (x21 + (0xf * x29));
  { uint64_t x32 = (uint64_t) (x31 >> 0x3b);
  { uint64_t x33 = ((uint64_t)x31 & 0x7ffffffffffffff);
  { uint64_t x34 = (x32 + x24);
  { uint64_t x35 = (x34 >> 0x3b);
  { uint64_t x36 = (x34 & 0x7ffffffffffffff);
  out[0] = x33;
  out[1] = x36;
  out[2] = (x35 + x27);
  out[3] = x30;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
