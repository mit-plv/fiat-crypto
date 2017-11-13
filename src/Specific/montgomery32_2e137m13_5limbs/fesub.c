static void fesub(uint32_t out[5], const uint32_t in1[5], const uint32_t in2[5]) {
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
  { uint32_t x21; uint8_t x22 = _subborrow_u32(0x0, x5, x13, &x21);
  { uint32_t x24; uint8_t x25 = _subborrow_u32(x22, x7, x15, &x24);
  { uint32_t x27; uint8_t x28 = _subborrow_u32(x25, x9, x17, &x27);
  { uint32_t x30; uint8_t x31 = _subborrow_u32(x28, x11, x19, &x30);
  { uint32_t x33; uint8_t x34 = _subborrow_u32(x31, x10, x18, &x33);
  { uint32_t x35 = cmovznz32(x34, 0x0, 0xffffffff);
  { uint32_t x36 = (x35 & 0xfffffff3);
  { uint32_t x38; uint8_t x39 = _addcarryx_u32(0x0, x21, x36, &x38);
  { uint32_t x40 = (x35 & 0xffffffff);
  { uint32_t x42; uint8_t x43 = _addcarryx_u32(x39, x24, x40, &x42);
  { uint32_t x44 = (x35 & 0xffffffff);
  { uint32_t x46; uint8_t x47 = _addcarryx_u32(x43, x27, x44, &x46);
  { uint32_t x48 = (x35 & 0xffffffff);
  { uint32_t x50; uint8_t x51 = _addcarryx_u32(x47, x30, x48, &x50);
  { uint32_t x52 = (x35 & 0x1ff);
  { uint32_t x54; uint8_t _ = _addcarryx_u32(x51, x33, x52, &x54);
  out[0] = x38;
  out[1] = x42;
  out[2] = x46;
  out[3] = x50;
  out[4] = x54;
  }}}}}}}}}}}}}}}}}}}}}}}}}}
}
