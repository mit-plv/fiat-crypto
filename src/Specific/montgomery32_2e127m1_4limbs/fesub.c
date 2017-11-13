static void fesub(uint32_t out[4], const uint32_t in1[4], const uint32_t in2[4]) {
  { const uint32_t x8 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x14 = in2[3];
  { const uint32_t x15 = in2[2];
  { const uint32_t x13 = in2[1];
  { const uint32_t x11 = in2[0];
  { uint32_t x17; uint8_t x18 = _subborrow_u32(0x0, x5, x11, &x17);
  { uint32_t x20; uint8_t x21 = _subborrow_u32(x18, x7, x13, &x20);
  { uint32_t x23; uint8_t x24 = _subborrow_u32(x21, x9, x15, &x23);
  { uint32_t x26; uint8_t x27 = _subborrow_u32(x24, x8, x14, &x26);
  { uint32_t x28 = cmovznz32(x27, 0x0, 0xffffffff);
  { uint32_t x29 = (x28 & 0xffffffff);
  { uint32_t x31; uint8_t x32 = _addcarryx_u32(0x0, x17, x29, &x31);
  { uint32_t x33 = (x28 & 0xffffffff);
  { uint32_t x35; uint8_t x36 = _addcarryx_u32(x32, x20, x33, &x35);
  { uint32_t x37 = (x28 & 0xffffffff);
  { uint32_t x39; uint8_t x40 = _addcarryx_u32(x36, x23, x37, &x39);
  { uint32_t x41 = (x28 & 0x7fffffff);
  { uint32_t x43; uint8_t _ = _addcarryx_u32(x40, x26, x41, &x43);
  out[0] = x31;
  out[1] = x35;
  out[2] = x39;
  out[3] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
