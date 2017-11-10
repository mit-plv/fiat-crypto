static void feadd(uint64_t out[5], const uint64_t in1[5], const uint64_t in2[5]) {
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
  { uint64_t x21; uint8_t x22 = _addcarryx_u64(0x0, x5, x13, &x21);
  { uint64_t x24; uint8_t x25 = _addcarryx_u64(x22, x7, x15, &x24);
  { uint64_t x27; uint8_t x28 = _addcarryx_u64(x25, x9, x17, &x27);
  { uint64_t x30; uint8_t x31 = _addcarryx_u64(x28, x11, x19, &x30);
  { uint64_t x33; uint8_t x34 = _addcarryx_u64(x31, x10, x18, &x33);
  { uint64_t x36; uint8_t x37 = _subborrow_u64(0x0, x21, 0xffffffffffffffedL, &x36);
  { uint64_t x39; uint8_t x40 = _subborrow_u64(x37, x24, 0xffffffffffffffffL, &x39);
  { uint64_t x42; uint8_t x43 = _subborrow_u64(x40, x27, 0xffffffffffffffffL, &x42);
  { uint64_t x45; uint8_t x46 = _subborrow_u64(x43, x30, 0xffffffffffffffffL, &x45);
  { uint64_t x48; uint8_t x49 = _subborrow_u64(x46, x33, 0x7ffffffff, &x48);
  { uint64_t _; uint8_t x52 = _subborrow_u64(x49, x34, 0x0, &_);
  { uint64_t x53 = cmovznz64(x52, x48, x33);
  { uint64_t x54 = cmovznz64(x52, x45, x30);
  { uint64_t x55 = cmovznz64(x52, x42, x27);
  { uint64_t x56 = cmovznz64(x52, x39, x24);
  { uint64_t x57 = cmovznz64(x52, x36, x21);
  out[0] = x57;
  out[1] = x56;
  out[2] = x55;
  out[3] = x54;
  out[4] = x53;
  }}}}}}}}}}}}}}}}}}}}}}}}}}
}
