static void feadd(uint32_t out[6], const uint32_t in1[6], const uint32_t in2[6]) {
  { const uint32_t x12 = in1[5];
  { const uint32_t x13 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x22 = in2[5];
  { const uint32_t x23 = in2[4];
  { const uint32_t x21 = in2[3];
  { const uint32_t x19 = in2[2];
  { const uint32_t x17 = in2[1];
  { const uint32_t x15 = in2[0];
  out[0] = (x5 + x15);
  out[1] = (x7 + x17);
  out[2] = (x9 + x19);
  out[3] = (x11 + x21);
  out[4] = (x13 + x23);
  out[5] = (x12 + x22);
  }}}}}}}}}}}}
}
