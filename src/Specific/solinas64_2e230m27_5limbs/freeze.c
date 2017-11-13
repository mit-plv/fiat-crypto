static void freeze(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x10, uint8_t x11 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0x3fffffffffe5);
  { uint64_t x13, uint8_t x14 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x11, Return x4, 0x3fffffffffff);
  { uint64_t x16, uint8_t x17 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x14, Return x6, 0x3fffffffffff);
  { uint64_t x19, uint8_t x20 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x17, Return x8, 0x3fffffffffff);
  { uint64_t x22, uint8_t x23 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x20, Return x7, 0x3fffffffffff);
  { uint64_t x24 = cmovznz64(x23, 0x0, 0xffffffffffffffffL);
  { uint64_t x25 = (x24 & 0x3fffffffffe5);
  { uint64_t x27, uint8_t x28 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x10, Return x25);
  { uint64_t x29 = (x24 & 0x3fffffffffff);
  { uint64_t x31, uint8_t x32 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x28, Return x13, Return x29);
  { uint64_t x33 = (x24 & 0x3fffffffffff);
  { uint64_t x35, uint8_t x36 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x32, Return x16, Return x33);
  { uint64_t x37 = (x24 & 0x3fffffffffff);
  { uint64_t x39, uint8_t x40 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x36, Return x19, Return x37);
  { uint64_t x41 = (x24 & 0x3fffffffffff);
  { uint64_t x43, uint8_t _ = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x40, Return x22, Return x41);
  out[0] = x27;
  out[1] = x31;
  out[2] = x35;
  out[3] = x39;
  out[4] = x43;
  }}}}}}}}}}}}}}}}}}}}}
}
