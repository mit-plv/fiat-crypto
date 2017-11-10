static void feadd(uint64_t out[2], const uint64_t in1[2], const uint64_t in2[2]) {
  { const uint64_t x4 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x6 = in2[1];
  { const uint64_t x7 = in2[0];
  { uint64_t x9; uint8_t x10 = _addcarryx_u64(0x0, x5, x7, &x9);
  { uint64_t x12; uint8_t x13 = _addcarryx_u64(x10, x4, x6, &x12);
  { uint64_t x15; uint8_t x16 = _subborrow_u64(0x0, x9, 0xffffffffffffffffL, &x15);
  { uint64_t x18; uint8_t x19 = _subborrow_u64(x16, x12, 0x7fffffffffffffffL, &x18);
  { uint64_t _; uint8_t x22 = _subborrow_u64(x19, x13, 0x0, &_);
  { uint64_t x23 = cmovznz64(x22, x18, x12);
  { uint64_t x24 = cmovznz64(x22, x15, x9);
  out[0] = x24;
  out[1] = x23;
  }}}}}}}}}}}
}
