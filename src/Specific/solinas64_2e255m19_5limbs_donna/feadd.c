static void feadd(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  out[0] = (x5 + x13);
  out[1] = (x7 + x15);
  out[2] = (x9 + x17);
  out[3] = (x11 + x19);
  out[4] = (x10 + x18);
  }}}}}}}}}}
}
