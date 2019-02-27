static void feopp(uint32_t out[7], const uint32_t in1[7]) {
  { const uint32_t x11 = in1[6];
  { const uint32_t x12 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x14; uint8_t/*bool*/ x15 = _subborrow_u32(0x0, 0x0, x2, &x14);
  { uint32_t x17; uint8_t/*bool*/ x18 = _subborrow_u32(x15, 0x0, x4, &x17);
  { uint32_t x20; uint8_t/*bool*/ x21 = _subborrow_u32(x18, 0x0, x6, &x20);
  { uint32_t x23; uint8_t/*bool*/ x24 = _subborrow_u32(x21, 0x0, x8, &x23);
  { uint32_t x26; uint8_t/*bool*/ x27 = _subborrow_u32(x24, 0x0, x10, &x26);
  { uint32_t x29; uint8_t/*bool*/ x30 = _subborrow_u32(x27, 0x0, x12, &x29);
  { uint32_t x32; uint8_t/*bool*/ x33 = _subborrow_u32(x30, 0x0, x11, &x32);
  { uint32_t x34 = cmovznz32(x33, 0x0, 0xffffffff);
  { uint8_t/*bool*/ x35 = (1&(uint8_t/*bool*/)x34 & 0x1);
  { uint32_t x37; uint8_t/*bool*/ x38 = _addcarryx_u32(0x0, x14, x35, &x37);
  { uint32_t x40; uint8_t/*bool*/ x41 = _addcarryx_u32(x38, x17, 0x0, &x40);
  { uint32_t x43; uint8_t/*bool*/ x44 = _addcarryx_u32(x41, x20, 0x0, &x43);
  { uint32_t x45 = (x34 & 0xffffffff);
  { uint32_t x47; uint8_t/*bool*/ x48 = _addcarryx_u32(x44, x23, x45, &x47);
  { uint32_t x49 = (x34 & 0xffffffff);
  { uint32_t x51; uint8_t/*bool*/ x52 = _addcarryx_u32(x48, x26, x49, &x51);
  { uint32_t x53 = (x34 & 0xffffffff);
  { uint32_t x55; uint8_t/*bool*/ x56 = _addcarryx_u32(x52, x29, x53, &x55);
  { uint32_t x57 = (x34 & 0xffffffff);
  { uint32_t x59; uint8_t/*bool*/ _ = _addcarryx_u32(x56, x32, x57, &x59);
  out[0] = x37;
  out[1] = x40;
  out[2] = x43;
  out[3] = x47;
  out[4] = x51;
  out[5] = x55;
  out[6] = x59;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}
}
