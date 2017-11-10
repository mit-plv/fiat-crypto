static void feopp(uint64_t out[6], const uint64_t in1[6]) {
  { const uint64_t x9 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x12; uint8_t x13 = _subborrow_u64(0x0, 0x0, x2, &x12);
  { uint64_t x15; uint8_t x16 = _subborrow_u64(x13, 0x0, x4, &x15);
  { uint64_t x18; uint8_t x19 = _subborrow_u64(x16, 0x0, x6, &x18);
  { uint64_t x21; uint8_t x22 = _subborrow_u64(x19, 0x0, x8, &x21);
  { uint64_t x24; uint8_t x25 = _subborrow_u64(x22, 0x0, x10, &x24);
  { uint64_t x27; uint8_t x28 = _subborrow_u64(x25, 0x0, x9, &x27);
  { uint64_t x29 = cmovznz64(x28, 0x0, 0xffffffffffffffffL);
  { uint64_t x30 = (x29 & 0xffffffffffffffffL);
  { uint64_t x32; uint8_t x33 = _addcarryx_u64(0x0, x12, x30, &x32);
  { uint64_t x34 = (x29 & 0xffffffffffffffffL);
  { uint64_t x36; uint8_t x37 = _addcarryx_u64(x33, x15, x34, &x36);
  { uint64_t x38 = (x29 & 0xffffffffffffffffL);
  { uint64_t x40; uint8_t x41 = _addcarryx_u64(x37, x18, x38, &x40);
  { uint64_t x42 = (x29 & 0xffffffffffffffffL);
  { uint64_t x44; uint8_t x45 = _addcarryx_u64(x41, x21, x42, &x44);
  { uint64_t x46 = (x29 & 0xffffffffffffffffL);
  { uint64_t x48; uint8_t x49 = _addcarryx_u64(x45, x24, x46, &x48);
  { uint64_t x50 = (x29 & 0xb0ffffffffffffffL);
  { uint64_t x52; uint8_t _ = _addcarryx_u64(x49, x27, x50, &x52);
  out[0] = x32;
  out[1] = x36;
  out[2] = x40;
  out[3] = x44;
  out[4] = x48;
  out[5] = x52;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
