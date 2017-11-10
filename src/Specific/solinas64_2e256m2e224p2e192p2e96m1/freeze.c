static void freeze(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x10, uint8_t x11 = Op (Syntax.SubWithGetBorrow 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0xfffffffffffff);
  { uint64_t x13; ℤ x14 = _subborrow_u51ℤ(x11, x4, 0xfffffffffff, &x13);
  { uint64_t x16; ℤ x17 = _subborrow_u51ℤ(x14, x6, 0x0, &x16);
  { uint64_t x19; ℤ x20 = _subborrow_u51ℤ(x17, x8, 0x4000000000, &x19);
  { uint64_t x22, uint8_t x23 = Op (Syntax.SubWithGetBorrow 51 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x20, Return x7, 0x7fffffff80000);
  { uint64_t x24 = cmovznz64(x23, 0x0, 0xffffffffffffffffL);
  { uint64_t x25 = (x24 & 0xfffffffffffff);
  { uint64_t x27, uint8_t x28 = Op (Syntax.AddWithGetCarry 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x10, Return x25);
  { uint64_t x29 = (x24 & 0xfffffffffff);
  { uint64_t x31; uint8_t x32 = _addcarryx_u51(x28, x13, x29, &x31);
  { uint64_t x34; uint8_t x35 = _addcarryx_u51(x32, x16, 0x0, &x34);
  { uint64_t x36 = (x24 & 0x4000000000);
  { uint64_t x38; uint8_t x39 = _addcarryx_u51(x35, x19, x36, &x38);
  { uint64_t x40 = (x24 & 0x7fffffff80000);
  { uint64_t x42; uint8_t _ = _addcarryx_u51(x39, x22, x40, &x42);
  out[0] = x27;
  out[1] = x31;
  out[2] = x34;
  out[3] = x38;
  out[4] = x42;
  }}}}}}}}}}}}}}}}}}}}
}
