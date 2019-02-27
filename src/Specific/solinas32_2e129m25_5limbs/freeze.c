static void freeze(uint32_t out[5], const uint32_t in1[5]) {
  { const uint32_t x7 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x10; uint8_t/*bool*/ x11 = _subborrow_u26(0x0, x2, 0x3ffffe7, &x10);
  { uint32_t x13; uint8_t/*bool*/ x14 = _subborrow_u26(x11, x4, 0x3ffffff, &x13);
  { uint32_t x16; uint8_t/*bool*/ x17 = _subborrow_u26(x14, x6, 0x3ffffff, &x16);
  { uint32_t x19; uint8_t/*bool*/ x20 = _subborrow_u26(x17, x8, 0x3ffffff, &x19);
  { uint32_t x22; uint8_t/*bool*/ x23 = _subborrow_u25(x20, x7, 0x1ffffff, &x22);
  { uint32_t x24 = cmovznz32(x23, 0x0, 0xffffffff);
  { uint32_t x25 = (x24 & 0x3ffffe7);
  { uint32_t x27; uint8_t/*bool*/ x28 = _addcarryx_u26(0x0, x10, x25, &x27);
  { uint32_t x29 = (x24 & 0x3ffffff);
  { uint32_t x31; uint8_t/*bool*/ x32 = _addcarryx_u26(x28, x13, x29, &x31);
  { uint32_t x33 = (x24 & 0x3ffffff);
  { uint32_t x35; uint8_t/*bool*/ x36 = _addcarryx_u26(x32, x16, x33, &x35);
  { uint32_t x37 = (x24 & 0x3ffffff);
  { uint32_t x39; uint8_t/*bool*/ x40 = _addcarryx_u26(x36, x19, x37, &x39);
  { uint32_t x41 = (x24 & 0x1ffffff);
  { uint32_t x43; uint8_t/*bool*/ _ = _addcarryx_u25(x40, x22, x41, &x43);
  out[0] = x27;
  out[1] = x31;
  out[2] = x35;
  out[3] = x39;
  out[4] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
