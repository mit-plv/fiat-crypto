static void fesub(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
  { const uint64_t x10 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x18 = in2[4];
  { const uint64_t x19 = in2[3];
  { const uint64_t x17 = in2[2];
  { const uint64_t x15 = in2[1];
  { const uint64_t x13 = in2[0];
  { uint64_t x21; uint8_t x22 = _subborrow_u64(0x0, x5, x13, &x21);
  { uint64_t x24; uint8_t x25 = _subborrow_u64(x22, x7, x15, &x24);
  { uint64_t x27; uint8_t x28 = _subborrow_u64(x25, x9, x17, &x27);
  { uint64_t x30; uint8_t x31 = _subborrow_u64(x28, x11, x19, &x30);
  { uint64_t x33; uint8_t x34 = _subborrow_u64(x31, x10, x18, &x33);
  { uint64_t x35 = cmovznz64(x34, 0x0, 0xffffffffffffffffL);
  { uint64_t x36 = (x35 & 0xfffffffffffffffdL);
  { uint64_t x38; uint8_t x39 = _addcarryx_u64(0x0, x21, x36, &x38);
  { uint64_t x40 = (x35 & 0xffffffffffffffffL);
  { uint64_t x42; uint8_t x43 = _addcarryx_u64(x39, x24, x40, &x42);
  { uint64_t x44 = (x35 & 0xffffffffffffffffL);
  { uint64_t x46; uint8_t x47 = _addcarryx_u64(x43, x27, x44, &x46);
  { uint64_t x48 = (x35 & 0xffffffffffffffffL);
  { uint64_t x50; uint8_t x51 = _addcarryx_u64(x47, x30, x48, &x50);
  { uint64_t x52 = (x35 & 0x3ff);
  { uint64_t x54; uint8_t _ = _addcarryx_u64(x51, x33, x52, &x54);
  out[0] = x38;
  out[1] = x42;
  out[2] = x46;
  out[3] = x50;
  out[4] = x54;
  }}}}}}}}}}}}}}}}}}}}}}}}}}
}
