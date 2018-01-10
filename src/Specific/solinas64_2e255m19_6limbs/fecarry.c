static void fecarry(uint64_t out[6], const uint64_t in1[6]) {
  { const uint64_t x9 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x11 = (x2 >> 0x2b);
  { uint64_t x12 = (x2 & 0x7ffffffffff);
  { uint64_t x13 = (x11 + x4);
  { uint64_t x14 = (x13 >> 0x2a);
  { uint64_t x15 = (x13 & 0x3ffffffffff);
  { uint64_t x16 = (x14 + x6);
  { uint64_t x17 = (x16 >> 0x2b);
  { uint64_t x18 = (x16 & 0x7ffffffffff);
  { uint64_t x19 = (x17 + x8);
  { uint64_t x20 = (x19 >> 0x2a);
  { uint64_t x21 = (x19 & 0x3ffffffffff);
  { uint64_t x22 = (x20 + x10);
  { uint64_t x23 = (x22 >> 0x2b);
  { uint64_t x24 = (x22 & 0x7ffffffffff);
  { uint64_t x25 = (x23 + x9);
  { uint64_t x26 = (x25 >> 0x2a);
  { uint64_t x27 = (x25 & 0x3ffffffffff);
  { uint64_t x28 = (x12 + (0x13 * x26));
  { uint64_t x29 = (x28 >> 0x2b);
  { uint64_t x30 = (x28 & 0x7ffffffffff);
  { uint64_t x31 = (x29 + x15);
  { uint64_t x32 = (x31 >> 0x2a);
  { uint64_t x33 = (x31 & 0x3ffffffffff);
  out[0] = x30;
  out[1] = x33;
  out[2] = (x32 + x18);
  out[3] = x21;
  out[4] = x24;
  out[5] = x27;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
