static void fecarry(uint64_t out[4], const uint64_t in1[4]) {
  { const uint64_t x5 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x7 = (x2 >> 0x35);
  { uint64_t x8 = (x2 & 0x1fffffffffffff);
  { uint64_t x9 = (x7 + x4);
  { uint64_t x10 = (x9 >> 0x35);
  { uint64_t x11 = (x9 & 0x1fffffffffffff);
  { uint64_t x12 = (x10 + x6);
  { uint64_t x13 = (x12 >> 0x35);
  { uint64_t x14 = (x12 & 0x1fffffffffffff);
  { uint64_t x15 = (x13 + x5);
  { uint64_t x16 = (x15 >> 0x35);
  { uint64_t x17 = (x15 & 0x1fffffffffffff);
  { uint64_t x18 = (x8 + (0x1d * x16));
  { uint64_t x19 = (x18 >> 0x35);
  { uint64_t x20 = (x18 & 0x1fffffffffffff);
  { uint64_t x21 = (x19 + x11);
  { uint64_t x22 = (x21 >> 0x35);
  { uint64_t x23 = (x21 & 0x1fffffffffffff);
  out[0] = x20;
  out[1] = x23;
  out[2] = (x22 + x14);
  out[3] = x17;
  }}}}}}}}}}}}}}}}}}}}}
}
