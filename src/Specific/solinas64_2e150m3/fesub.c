static void fesub(uint64_t out[3], const uint64_t in1[3], const uint64_t in2[3]) {
  { const uint64_t x6 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x10 = in2[2];
  { const uint64_t x11 = in2[1];
  { const uint64_t x9 = in2[0];
  out[0] = ((0x7fffffffffffa + x5) - x9);
  out[1] = ((0x7fffffffffffe + x7) - x11);
  out[2] = ((0x7fffffffffffe + x6) - x10);
  }}}}}}
}
