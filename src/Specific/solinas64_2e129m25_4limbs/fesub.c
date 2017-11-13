static void fesub(uint64_t out[4], const uint64_t in1[4], const uint64_t in2[4]) {
  { const uint64_t x8 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x14 = in2[3];
  { const uint64_t x15 = in2[2];
  { const uint64_t x13 = in2[1];
  { const uint64_t x11 = in2[0];
  out[0] = ((Const 17179869134 + x5) - x11);
  out[1] = ((Const 8589934590 + x7) - x13);
  out[2] = ((Const 8589934590 + x9) - x15);
  out[3] = ((Const 8589934590 + x8) - x14);
  }}}}}}}}
}
