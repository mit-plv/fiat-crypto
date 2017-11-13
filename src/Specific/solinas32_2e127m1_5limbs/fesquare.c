static void fesquare(uint32_t out[5], const uint32_t in1[5]) {
  { const uint32_t x7 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint64_t x9 = (((uint64_t)x2 * x7) + ((0x2 * ((uint64_t)x4 * x8)) + (((uint64_t)x6 * x6) + ((0x2 * ((uint64_t)x8 * x4)) + ((uint64_t)x7 * x2)))));
  { uint64_t x10 = ((((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))) + ((uint64_t)x7 * x7));
  { uint64_t x11 = ((((uint64_t)x2 * x6) + ((0x2 * ((uint64_t)x4 * x4)) + ((uint64_t)x6 * x2))) + ((0x2 * ((uint64_t)x8 * x7)) + (0x2 * ((uint64_t)x7 * x8))));
  { uint64_t x12 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (((uint64_t)x6 * x7) + ((0x2 * ((uint64_t)x8 * x8)) + ((uint64_t)x7 * x6))));
  { uint64_t x13 = (((uint64_t)x2 * x2) + ((0x2 * ((uint64_t)x4 * x7)) + ((0x2 * ((uint64_t)x6 * x8)) + ((0x2 * ((uint64_t)x8 * x6)) + (0x2 * ((uint64_t)x7 * x4))))));
  { uint32_t x14 = (uint32_t) (x13 >> 0x1a);
  { uint32_t x15 = ((uint32_t)x13 & 0x3ffffff);
  { uint64_t x16 = (x14 + x12);
  { uint32_t x17 = (uint32_t) (x16 >> 0x19);
  { uint32_t x18 = ((uint32_t)x16 & 0x1ffffff);
  { uint64_t x19 = (x17 + x11);
  { uint32_t x20 = (uint32_t) (x19 >> 0x1a);
  { uint32_t x21 = ((uint32_t)x19 & 0x3ffffff);
  { uint64_t x22 = (x20 + x10);
  { uint32_t x23 = (uint32_t) (x22 >> 0x19);
  { uint32_t x24 = ((uint32_t)x22 & 0x1ffffff);
  { uint64_t x25 = (x23 + x9);
  { uint64_t x26 = (x25 >> 0x19);
  { uint32_t x27 = ((uint32_t)x25 & 0x1ffffff);
  { uint64_t x28 = (x15 + x26);
  { uint32_t x29 = (uint32_t) (x28 >> 0x1a);
  { uint32_t x30 = ((uint32_t)x28 & 0x3ffffff);
  { uint32_t x31 = (x29 + x18);
  { uint32_t x32 = (x31 >> 0x19);
  { uint32_t x33 = (x31 & 0x1ffffff);
  out[0] = x30;
  out[1] = x33;
  out[2] = (x32 + x21);
  out[3] = x24;
  out[4] = x27;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
