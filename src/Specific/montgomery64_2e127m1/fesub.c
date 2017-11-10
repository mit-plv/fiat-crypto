static void fesub(uint64_t out[2], const uint64_t in1[2], const uint64_t in2[2]) {
  { const uint64_t x4 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x6 = in2[1];
  { const uint64_t x7 = in2[0];
  { uint64_t x9; uint8_t x10 = _subborrow_u64(0x0, x5, x7, &x9);
  { uint64_t x12; uint8_t x13 = _subborrow_u64(x10, x4, x6, &x12);
  { uint64_t x14 = cmovznz64(x13, 0x0, 0xffffffffffffffffL);
  { uint64_t x15 = (x14 & 0xffffffffffffffffL);
  { uint64_t x17; uint8_t x18 = _addcarryx_u64(0x0, x9, x15, &x17);
  { uint64_t x19 = (x14 & 0x7fffffffffffffffL);
  { uint64_t x21; uint8_t _ = _addcarryx_u64(x18, x12, x19, &x21);
  out[0] = x17;
  out[1] = x21;
  }}}}}}}}}}}
}
