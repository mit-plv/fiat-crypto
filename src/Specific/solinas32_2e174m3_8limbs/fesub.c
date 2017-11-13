static void fesub(uint32_t out[8], const uint32_t in1[8], const uint32_t in2[8]) {
  { const uint32_t x16 = in1[7];
  { const uint32_t x17 = in1[6];
  { const uint32_t x15 = in1[5];
  { const uint32_t x13 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x30 = in2[7];
  { const uint32_t x31 = in2[6];
  { const uint32_t x29 = in2[5];
  { const uint32_t x27 = in2[4];
  { const uint32_t x25 = in2[3];
  { const uint32_t x23 = in2[2];
  { const uint32_t x21 = in2[1];
  { const uint32_t x19 = in2[0];
  out[0] = ((Const 8388602 + x5) - x19);
  out[1] = ((0x7ffffe + x7) - x21);
  out[2] = ((0x7ffffe + x9) - x23);
  out[3] = ((0x3ffffe + x11) - x25);
  out[4] = ((0x7ffffe + x13) - x27);
  out[5] = ((0x7ffffe + x15) - x29);
  out[6] = ((0x7ffffe + x17) - x31);
  out[7] = ((0x3ffffe + x16) - x30);
  }}}}}}}}}}}}}}}}
}
