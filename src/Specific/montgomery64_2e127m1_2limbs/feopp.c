static void feopp(uint64_t out[2], const uint64_t in1[2]) {
  { const uint64_t x1 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x4; uint8_t x5 = _subborrow_u64(0x0, 0x0, x2, &x4);
  { uint64_t x7; uint8_t x8 = _subborrow_u64(x5, 0x0, x1, &x7);
  { uint64_t x9 = cmovznz64(x8, 0x0, 0xffffffffffffffffL);
  { uint64_t x10 = (x9 & 0xffffffffffffffffL);
  { uint64_t x12; uint8_t x13 = _addcarryx_u64(0x0, x4, x10, &x12);
  { uint64_t x14 = (x9 & 0x7fffffffffffffffL);
  { uint64_t x16; uint8_t _ = _addcarryx_u64(x13, x7, x14, &x16);
  out[0] = x12;
  out[1] = x16;
  }}}}}}}}}
}
