static void fesub(uint64_t out[3], const uint64_t in1[3], const uint64_t in2[3]) {
  { const uint64_t x6 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x10 = in2[2];
  { const uint64_t x11 = in2[1];
  { const uint64_t x9 = in2[0];
  { uint64_t x13; uint8_t x14 = _subborrow_u64(0x0, x5, x9, &x13);
  { uint64_t x16; uint8_t x17 = _subborrow_u64(x14, x7, x11, &x16);
  { uint64_t x19; uint8_t x20 = _subborrow_u64(x17, x6, x10, &x19);
  { uint64_t x21 = cmovznz64(x20, 0x0, 0xffffffffffffffffL);
  { uint64_t x22 = (x21 & 0xfffffffffffffff3L);
  { uint64_t x24; uint8_t x25 = _addcarryx_u64(0x0, x13, x22, &x24);
  { uint64_t x26 = (x21 & 0xffffffffffffffffL);
  { uint64_t x28; uint8_t x29 = _addcarryx_u64(x25, x16, x26, &x28);
  { uint64_t x30 = (x21 & 0x1ff);
  { uint64_t x32; uint8_t _ = _addcarryx_u64(x29, x19, x30, &x32);
  out[0] = x24;
  out[1] = x28;
  out[2] = x32;
  }}}}}}}}}}}}}}}}
}
