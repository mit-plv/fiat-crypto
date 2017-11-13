static void feadd(uint64_t out[4], const uint64_t in1[4], const uint64_t in2[4]) {
  { const uint64_t x8 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x14 = in2[3];
  { const uint64_t x15 = in2[2];
  { const uint64_t x13 = in2[1];
  { const uint64_t x11 = in2[0];
  { uint64_t x17; uint8_t x18 = _addcarryx_u64(0x0, x5, x11, &x17);
  { uint64_t x20; uint8_t x21 = _addcarryx_u64(x18, x7, x13, &x20);
  { uint64_t x23; uint8_t x24 = _addcarryx_u64(x21, x9, x15, &x23);
  { uint64_t x26; uint8_t x27 = _addcarryx_u64(x24, x8, x14, &x26);
  { uint64_t x29; uint8_t x30 = _subborrow_u64(0x0, x17, 0xffffffffffffffdfL, &x29);
  { uint64_t x32; uint8_t x33 = _subborrow_u64(x30, x20, 0xffffffffffffffffL, &x32);
  { uint64_t x35; uint8_t x36 = _subborrow_u64(x33, x23, 0xffffffffffffffffL, &x35);
  { uint64_t x38; uint8_t x39 = _subborrow_u64(x36, x26, 0x3, &x38);
  { uint64_t _; uint8_t x42 = _subborrow_u64(x39, x27, 0x0, &_);
  { uint64_t x43 = cmovznz64(x42, x38, x26);
  { uint64_t x44 = cmovznz64(x42, x35, x23);
  { uint64_t x45 = cmovznz64(x42, x32, x20);
  { uint64_t x46 = cmovznz64(x42, x29, x17);
  out[0] = x46;
  out[1] = x45;
  out[2] = x44;
  out[3] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
