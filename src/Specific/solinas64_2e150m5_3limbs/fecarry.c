static void fecarry(uint64_t out[3], const uint64_t in1[3]) {
  { const uint64_t x3 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x5 = (x2 >> 0x32);
  { uint64_t x6 = (x2 & 0x3ffffffffffff);
  { uint64_t x7 = (x5 + x4);
  { uint64_t x8 = (x7 >> 0x32);
  { uint64_t x9 = (x7 & 0x3ffffffffffff);
  { uint64_t x10 = (x8 + x3);
  { uint64_t x11 = (x10 >> 0x32);
  { uint64_t x12 = (x10 & 0x3ffffffffffff);
  { uint64_t x13 = (x6 + (0x5 * x11));
  { uint64_t x14 = (x13 >> 0x32);
  { uint64_t x15 = (x13 & 0x3ffffffffffff);
  { uint64_t x16 = (x14 + x9);
  { uint64_t x17 = (x16 >> 0x32);
  { uint64_t x18 = (x16 & 0x3ffffffffffff);
  out[0] = x15;
  out[1] = x18;
  out[2] = (x17 + x12);
  }}}}}}}}}}}}}}}}}
}
