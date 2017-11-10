static void freeze(uint64_t out[4], const uint64_t in1[4]) {
  { const uint64_t x5 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x8, uint8_t x9 = Op (Syntax.SubWithGetBorrow 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0xffffffffffffb);
  { uint64_t x11; uint8_t x12 = _subborrow_u51(x9, x4, 0x7ffffffffffff, &x11);
  { uint64_t x14, uint8_t x15 = Op (Syntax.SubWithGetBorrow 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x12, Return x6, 0xfffffffffffff);
  { uint64_t x17; uint8_t x18 = _subborrow_u51(x15, x5, 0x7ffffffffffff, &x17);
  { uint64_t x19 = cmovznz64(x18, 0x0, 0xffffffffffffffffL);
  { uint64_t x20 = (x19 & 0xffffffffffffb);
  { uint64_t x22, uint8_t x23 = Op (Syntax.AddWithGetCarry 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x8, Return x20);
  { uint64_t x24 = (x19 & 0x7ffffffffffff);
  { uint64_t x26; uint8_t x27 = _addcarryx_u51(x23, x11, x24, &x26);
  { uint64_t x28 = (x19 & 0xfffffffffffff);
  { uint64_t x30, uint8_t x31 = Op (Syntax.AddWithGetCarry 52 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x27, Return x14, Return x28);
  { uint64_t x32 = (x19 & 0x7ffffffffffff);
  { uint64_t x34; uint8_t _ = _addcarryx_u51(x31, x17, x32, &x34);
  out[0] = x22;
  out[1] = x26;
  out[2] = x30;
  out[3] = x34;
  }}}}}}}}}}}}}}}}}
}
