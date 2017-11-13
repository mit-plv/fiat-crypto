static void feopp(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x10; uint8_t x11 = _subborrow_u64(0x0, 0x0, x2, &x10);
  { uint64_t x13; uint8_t x14 = _subborrow_u64(x11, 0x0, x4, &x13);
  { uint64_t x16; uint8_t x17 = _subborrow_u64(x14, 0x0, x6, &x16);
  { uint64_t x19; uint8_t x20 = _subborrow_u64(x17, 0x0, x8, &x19);
  { uint64_t x22; uint8_t x23 = _subborrow_u64(x20, 0x0, x7, &x22);
  { uint64_t x24 = cmovznz64(x23, 0x0, 0xffffffffffffffffL);
  { uint64_t x25 = (x24 & 0xfffffffffffffff7L);
  { uint64_t x27; uint8_t x28 = _addcarryx_u64(0x0, x10, x25, &x27);
  { uint64_t x29 = (x24 & 0xffffffffffffffffL);
  { uint64_t x31; uint8_t x32 = _addcarryx_u64(x28, x13, x29, &x31);
  { uint64_t x33 = (x24 & 0xffffffffffffffffL);
  { uint64_t x35; uint8_t x36 = _addcarryx_u64(x32, x16, x33, &x35);
  { uint64_t x37 = (x24 & 0xffffffffffffffffL);
  { uint64_t x39; uint8_t x40 = _addcarryx_u64(x36, x19, x37, &x39);
  { uint64_t x41 = (x24 & 0x1fffffff);
  { uint64_t x43; uint8_t _ = _addcarryx_u64(x40, x22, x41, &x43);
  out[0] = x27;
  out[1] = x31;
  out[2] = x35;
  out[3] = x39;
  out[4] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
