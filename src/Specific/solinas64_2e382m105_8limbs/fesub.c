static void fesub(uint64_t out[8], const uint64_t in1[8], const uint64_t in2[8]) {
  { const uint64_t x16 = in1[7];
  { const uint64_t x17 = in1[6];
  { const uint64_t x15 = in1[5];
  { const uint64_t x13 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x30 = in2[7];
  { const uint64_t x31 = in2[6];
  { const uint64_t x29 = in2[5];
  { const uint64_t x27 = in2[4];
  { const uint64_t x25 = in2[3];
  { const uint64_t x23 = in2[2];
  { const uint64_t x21 = in2[1];
  { const uint64_t x19 = in2[0];
  out[0] = ((Const 562949953421102 + x5) - x19);
  out[1] = ((0x1fffffffffffe + x7) - x21);
  out[2] = ((0x1fffffffffffe + x9) - x23);
  out[3] = ((0xfffffffffffe + x11) - x25);
  out[4] = ((0x1fffffffffffe + x13) - x27);
  out[5] = ((0x1fffffffffffe + x15) - x29);
  out[6] = ((0x1fffffffffffe + x17) - x31);
  out[7] = ((0xfffffffffffe + x16) - x30);
  }}}}}}}}}}}}}}}}
}
