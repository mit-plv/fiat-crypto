static void freeze(uint64_t out[6], const uint64_t in1[6]) {
  { const uint64_t x9 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x12, uint8_t/*bool*/ x13 = Op (Syntax.SubWithGetBorrow 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (0x0, Return x2, 0x7ffffffffed);
  { uint64_t x15, uint8_t/*bool*/ x16 = Op (Syntax.SubWithGetBorrow 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x13, Return x4, 0x3ffffffffff);
  { uint64_t x18, uint8_t/*bool*/ x19 = Op (Syntax.SubWithGetBorrow 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x16, Return x6, 0x7ffffffffff);
  { uint64_t x21, uint8_t/*bool*/ x22 = Op (Syntax.SubWithGetBorrow 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x19, Return x8, 0x3ffffffffff);
  { uint64_t x24, uint8_t/*bool*/ x25 = Op (Syntax.SubWithGetBorrow 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x22, Return x10, 0x7ffffffffff);
  { uint64_t x27, uint8_t/*bool*/ x28 = Op (Syntax.SubWithGetBorrow 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x25, Return x9, 0x3ffffffffff);
  { uint64_t x29 = cmovznz64(x28, 0x0, 0xffffffffffffffffL);
  { uint64_t x30 = (x29 & 0x7ffffffffed);
  { uint64_t x32, uint8_t/*bool*/ x33 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (0x0, Return x12, Return x30);
  { uint64_t x34 = (x29 & 0x3ffffffffff);
  { uint64_t x36, uint8_t/*bool*/ x37 = Op (Syntax.AddWithGetCarry 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x33, Return x15, Return x34);
  { uint64_t x38 = (x29 & 0x7ffffffffff);
  { uint64_t x40, uint8_t/*bool*/ x41 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x37, Return x18, Return x38);
  { uint64_t x42 = (x29 & 0x3ffffffffff);
  { uint64_t x44, uint8_t/*bool*/ x45 = Op (Syntax.AddWithGetCarry 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x41, Return x21, Return x42);
  { uint64_t x46 = (x29 & 0x7ffffffffff);
  { uint64_t x48, uint8_t/*bool*/ x49 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x45, Return x24, Return x46);
  { uint64_t x50 = (x29 & 0x3ffffffffff);
  { uint64_t x52, uint8_t/*bool*/ _ = Op (Syntax.AddWithGetCarry 42 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x49, Return x27, Return x50);
  out[0] = x32;
  out[1] = x36;
  out[2] = x40;
  out[3] = x44;
  out[4] = x48;
  out[5] = x52;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
