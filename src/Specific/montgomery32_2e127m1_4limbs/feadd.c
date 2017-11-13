static void feadd(uint32_t out[4], const uint32_t in1[4], const uint32_t in2[4]) {
  { const uint32_t x8 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x14 = in2[3];
  { const uint32_t x15 = in2[2];
  { const uint32_t x13 = in2[1];
  { const uint32_t x11 = in2[0];
  { uint32_t x17; uint8_t x18 = _addcarryx_u32(0x0, x5, x11, &x17);
  { uint32_t x20; uint8_t x21 = _addcarryx_u32(x18, x7, x13, &x20);
  { uint32_t x23; uint8_t x24 = _addcarryx_u32(x21, x9, x15, &x23);
  { uint32_t x26; uint8_t x27 = _addcarryx_u32(x24, x8, x14, &x26);
  { uint32_t x29; uint8_t x30 = _subborrow_u32(0x0, x17, 0xffffffff, &x29);
  { uint32_t x32; uint8_t x33 = _subborrow_u32(x30, x20, 0xffffffff, &x32);
  { uint32_t x35; uint8_t x36 = _subborrow_u32(x33, x23, 0xffffffff, &x35);
  { uint32_t x38; uint8_t x39 = _subborrow_u32(x36, x26, 0x7fffffff, &x38);
  { uint32_t _; uint8_t x42 = _subborrow_u32(x39, x27, 0x0, &_);
  { uint32_t x43 = cmovznz32(x42, x38, x26);
  { uint32_t x44 = cmovznz32(x42, x35, x23);
  { uint32_t x45 = cmovznz32(x42, x32, x20);
  { uint32_t x46 = cmovznz32(x42, x29, x17);
  out[0] = x46;
  out[1] = x45;
  out[2] = x44;
  out[3] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
