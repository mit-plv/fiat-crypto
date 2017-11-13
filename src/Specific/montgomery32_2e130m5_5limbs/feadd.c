static void feadd(uint32_t out[5], const uint32_t in1[5], const uint32_t in2[5]) {
  { const uint32_t x10 = in1[4];
  { const uint32_t x11 = in1[3];
  { const uint32_t x9 = in1[2];
  { const uint32_t x7 = in1[1];
  { const uint32_t x5 = in1[0];
  { const uint32_t x18 = in2[4];
  { const uint32_t x19 = in2[3];
  { const uint32_t x17 = in2[2];
  { const uint32_t x15 = in2[1];
  { const uint32_t x13 = in2[0];
  { uint32_t x21; uint8_t x22 = _addcarryx_u32(0x0, x5, x13, &x21);
  { uint32_t x24; uint8_t x25 = _addcarryx_u32(x22, x7, x15, &x24);
  { uint32_t x27; uint8_t x28 = _addcarryx_u32(x25, x9, x17, &x27);
  { uint32_t x30; uint8_t x31 = _addcarryx_u32(x28, x11, x19, &x30);
  { uint32_t x33; uint8_t x34 = _addcarryx_u32(x31, x10, x18, &x33);
  { uint32_t x36; uint8_t x37 = _subborrow_u32(0x0, x21, 0xfffffffb, &x36);
  { uint32_t x39; uint8_t x40 = _subborrow_u32(x37, x24, 0xffffffff, &x39);
  { uint32_t x42; uint8_t x43 = _subborrow_u32(x40, x27, 0xffffffff, &x42);
  { uint32_t x45; uint8_t x46 = _subborrow_u32(x43, x30, 0xffffffff, &x45);
  { uint32_t x48; uint8_t x49 = _subborrow_u32(x46, x33, 0x3, &x48);
  { uint32_t _; uint8_t x52 = _subborrow_u32(x49, x34, 0x0, &_);
  { uint32_t x53 = cmovznz32(x52, x48, x33);
  { uint32_t x54 = cmovznz32(x52, x45, x30);
  { uint32_t x55 = cmovznz32(x52, x42, x27);
  { uint32_t x56 = cmovznz32(x52, x39, x24);
  { uint32_t x57 = cmovznz32(x52, x36, x21);
  out[0] = x57;
  out[1] = x56;
  out[2] = x55;
  out[3] = x54;
  out[4] = x53;
  }}}}}}}}}}}}}}}}}}}}}}}}}}
}
