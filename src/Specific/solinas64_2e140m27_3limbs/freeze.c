static void freeze(uint64_t out[3], const uint64_t in1[3]) {
  { const uint64_t x3 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x6, uint8_t x7 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0x7fffffffffe5);
  { uint64_t x9, uint8_t x10 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x7, Return x4, 0x7fffffffffff);
  { uint64_t x12, uint8_t x13 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x10, Return x3, 0x3fffffffffff);
  { uint64_t x14 = cmovznz64(x13, 0x0, 0xffffffffffffffffL);
  { uint64_t x15 = (x14 & 0x7fffffffffe5);
  { uint64_t x17, uint8_t x18 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x6, Return x15);
  { uint64_t x19 = (x14 & 0x7fffffffffff);
  { uint64_t x21, uint8_t x22 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x18, Return x9, Return x19);
  { uint64_t x23 = (x14 & 0x3fffffffffff);
  { uint64_t x25, uint8_t _ = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x22, Return x12, Return x23);
  out[0] = x17;
  out[1] = x21;
  out[2] = x25;
  }}}}}}}}}}}}}
}
