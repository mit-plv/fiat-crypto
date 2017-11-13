static void freeze(uint64_t out[4], const uint64_t in1[4]) {
  { const uint64_t x5 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x8, uint8_t x9 = Op (Syntax.SubWithGetBorrow 36 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0xffffffff7);
  { uint64_t x11, uint8_t x12 = Op (Syntax.SubWithGetBorrow 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x9, Return x4, 0x7ffffffff);
  { uint64_t x14, uint8_t x15 = Op (Syntax.SubWithGetBorrow 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x12, Return x6, 0x7ffffffff);
  { uint64_t x17, uint8_t x18 = Op (Syntax.SubWithGetBorrow 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x15, Return x5, 0x7ffffffff);
  { uint64_t x19 = cmovznz64(x18, 0x0, 0xffffffffffffffffL);
  { uint64_t x20 = (x19 & 0xffffffff7);
  { uint64_t x22, uint8_t x23 = Op (Syntax.AddWithGetCarry 36 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x8, Return x20);
  { uint64_t x24 = (x19 & 0x7ffffffff);
  { uint64_t x26, uint8_t x27 = Op (Syntax.AddWithGetCarry 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x23, Return x11, Return x24);
  { uint64_t x28 = (x19 & 0x7ffffffff);
  { uint64_t x30, uint8_t x31 = Op (Syntax.AddWithGetCarry 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x27, Return x14, Return x28);
  { uint64_t x32 = (x19 & 0x7ffffffff);
  { uint64_t x34, uint8_t _ = Op (Syntax.AddWithGetCarry 35 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x31, Return x17, Return x32);
  out[0] = x22;
  out[1] = x26;
  out[2] = x30;
  out[3] = x34;
  }}}}}}}}}}}}}}}}}
}
