static void fesub(uint32_t out[7], const uint32_t in1[7], const uint32_t in2[7]) {
  { const uint32_t x14 = in1[6];
  { const uint32_t x15 = in1[5];
  { const uint32_t x13 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x26 = in2[6];
  { const uint32_t x27 = in2[5];
  { const uint32_t x25 = in2[4];
  { const uint32_t x23 = in2[3];
  { const uint32_t x21 = in2[2];
  { const uint32_t x19 = in2[1];
  { const uint32_t x17 = in2[0];
  out[0] = ((0x3ffffde + x5) - x17);
  out[1] = ((0x3fffffe + x7) - x19);
  out[2] = ((0x3fffffe + x9) - x21);
  out[3] = ((0x3fffffe + x11) - x23);
  out[4] = ((0x3fffffe + x13) - x25);
  out[5] = ((0x3fffffe + x15) - x27);
  out[6] = ((0x1fffffe + x14) - x26);
  }}}}}}}}}}}}}}
}
