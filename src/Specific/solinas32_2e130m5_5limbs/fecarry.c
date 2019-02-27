static void fecarry(uint32_t out[5], const uint32_t in1[5]) {
  { const uint32_t x7 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x9 = (x2 >> 0x1a);
  { uint32_t x10 = (x2 & 0x3ffffff);
  { uint32_t x11 = (x9 + x4);
  { uint32_t x12 = (x11 >> 0x1a);
  { uint32_t x13 = (x11 & 0x3ffffff);
  { uint32_t x14 = (x12 + x6);
  { uint32_t x15 = (x14 >> 0x1a);
  { uint32_t x16 = (x14 & 0x3ffffff);
  { uint32_t x17 = (x15 + x8);
  { uint32_t x18 = (x17 >> 0x1a);
  { uint32_t x19 = (x17 & 0x3ffffff);
  { uint32_t x20 = (x18 + x7);
  { uint32_t x21 = (x20 >> 0x1a);
  { uint32_t x22 = (x20 & 0x3ffffff);
  { uint32_t x23 = (x10 + (0x5 * x21));
  { uint32_t x24 = (x23 >> 0x1a);
  { uint32_t x25 = (x23 & 0x3ffffff);
  { uint32_t x26 = (x24 + x13);
  { uint32_t x27 = (x26 >> 0x1a);
  { uint32_t x28 = (x26 & 0x3ffffff);
  out[0] = x25;
  out[1] = x28;
  out[2] = (x27 + x16);
  out[3] = x19;
  out[4] = x22;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
