static void feopp(uint64_t out[3], const uint64_t in1[3]) {
  { const uint64_t x3 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x6; uint8_t x7 = _subborrow_u64(0x0, 0x0, x2, &x6);
  { uint64_t x9; uint8_t x10 = _subborrow_u64(x7, 0x0, x4, &x9);
  { uint64_t x12; uint8_t x13 = _subborrow_u64(x10, 0x0, x3, &x12);
  { uint64_t x14 = cmovznz64(x13, 0x0, 0xffffffffffffffffL);
  { uint64_t x15 = (x14 & 0xffffffffffffffefL);
  { uint64_t x17; uint8_t x18 = _addcarryx_u64(0x0, x6, x15, &x17);
  { uint64_t x19 = (x14 & 0xffffffffffffffffL);
  { uint64_t x21; uint8_t x22 = _addcarryx_u64(x18, x9, x19, &x21);
  { uint64_t x23 = (x14 & 0xffffff);
  { uint64_t x25; uint8_t _ = _addcarryx_u64(x22, x12, x23, &x25);
  out[0] = x17;
  out[1] = x21;
  out[2] = x25;
  }}}}}}}}}}}}}
}
