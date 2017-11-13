static void feadd(uint64_t out[3], const uint64_t in1[3], const uint64_t in2[3]) {
  { const uint64_t x6 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x10 = in2[2];
  { const uint64_t x11 = in2[1];
  { const uint64_t x9 = in2[0];
  { uint64_t x13; uint8_t x14 = _addcarryx_u64(0x0, x5, x9, &x13);
  { uint64_t x16; uint8_t x17 = _addcarryx_u64(x14, x7, x11, &x16);
  { uint64_t x19; uint8_t x20 = _addcarryx_u64(x17, x6, x10, &x19);
  { uint64_t x22; uint8_t x23 = _subborrow_u64(0x0, x13, 0xffffffffffffffefL, &x22);
  { uint64_t x25; uint8_t x26 = _subborrow_u64(x23, x16, 0xffffffffffffffffL, &x25);
  { uint64_t x28; uint8_t x29 = _subborrow_u64(x26, x19, 0x3fffffffffff, &x28);
  { uint64_t _; uint8_t x32 = _subborrow_u64(x29, x20, 0x0, &_);
  { uint64_t x33 = cmovznz64(x32, x28, x19);
  { uint64_t x34 = cmovznz64(x32, x25, x16);
  { uint64_t x35 = cmovznz64(x32, x22, x13);
  out[0] = x35;
  out[1] = x34;
  out[2] = x33;
  }}}}}}}}}}}}}}}}
}
