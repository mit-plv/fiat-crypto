static void fesub(uint32_t out[5], const uint32_t in1[5], const uint32_t in2[5]) {
  { const uint32_t x10 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x18 = in2[4];
  { const uint32_t x19 = in2[3];
  { const uint32_t x17 = in2[2];
  { const uint32_t x15 = in2[1];
  { const uint32_t x13 = in2[0];
  out[0] = ((Const 536870886 + x5) - x13);
  out[1] = ((0xffffffe + x7) - x15);
  out[2] = ((0x1ffffffe + x9) - x17);
  out[3] = ((0xffffffe + x11) - x19);
  out[4] = ((0xffffffe + x10) - x18);
  }}}}}}}}}}
}
