static void fecarry(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x9 = (x2 >> 0x33);
  { uint64_t x10 = (x2 & 0x7ffffffffffff);
  { uint64_t x11 = (x9 + x4);
  { uint64_t x12 = (x11 >> 0x33);
  { uint64_t x13 = (x11 & 0x7ffffffffffff);
  { uint64_t x14 = (x12 + x6);
  { uint64_t x15 = (x14 >> 0x33);
  { uint64_t x16 = (x14 & 0x7ffffffffffff);
  { uint64_t x17 = (x15 + x8);
  { uint64_t x18 = (x17 >> 0x33);
  { uint64_t x19 = (x17 & 0x7ffffffffffff);
  { uint64_t x20 = (x18 + x7);
  { uint64_t x21 = (x20 >> 0x33);
  { uint64_t x22 = (x20 & 0x7ffffffffffff);
  { uint64_t x23 = (x10 + (0x13 * x21));
  { uint64_t x24 = (x23 >> 0x33);
  { uint64_t x25 = (x23 & 0x7ffffffffffff);
  { uint64_t x26 = (x24 + x13);
  { uint64_t x27 = (x26 >> 0x33);
  { uint64_t x28 = (x26 & 0x7ffffffffffff);
  out[0] = x25;
  out[1] = x28;
  out[2] = (x27 + x16);
  out[3] = x19;
  out[4] = x22;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
