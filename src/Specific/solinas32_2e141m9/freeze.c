static void freeze(uint32_t out[6], const uint32_t in1[6]) {
  { const uint32_t x9 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x12, uint8_t x13 = Op (Syntax.SubWithGetBorrow 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (0x0, Return x2, 0xfffff7);
  { uint32_t x15, uint8_t x16 = Op (Syntax.SubWithGetBorrow 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x13, Return x4, 0x7fffff);
  { uint32_t x18, uint8_t x19 = Op (Syntax.SubWithGetBorrow 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x16, Return x6, 0xffffff);
  { uint32_t x21, uint8_t x22 = Op (Syntax.SubWithGetBorrow 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x19, Return x8, 0x7fffff);
  { uint32_t x24, uint8_t x25 = Op (Syntax.SubWithGetBorrow 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x22, Return x10, 0xffffff);
  { uint32_t x27, uint8_t x28 = Op (Syntax.SubWithGetBorrow 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x25, Return x9, 0x7fffff);
  { uint32_t x29 = cmovznz32(x28, 0x0, 0xffffffff);
  { uint32_t x30 = (x29 & 0xfffff7);
  { uint32_t x32, uint8_t x33 = Op (Syntax.AddWithGetCarry 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (0x0, Return x12, Return x30);
  { uint32_t x34 = (x29 & 0x7fffff);
  { uint32_t x36, uint8_t x37 = Op (Syntax.AddWithGetCarry 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x33, Return x15, Return x34);
  { uint32_t x38 = (x29 & 0xffffff);
  { uint32_t x40, uint8_t x41 = Op (Syntax.AddWithGetCarry 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x37, Return x18, Return x38);
  { uint32_t x42 = (x29 & 0x7fffff);
  { uint32_t x44, uint8_t x45 = Op (Syntax.AddWithGetCarry 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x41, Return x21, Return x42);
  { uint32_t x46 = (x29 & 0xffffff);
  { uint32_t x48, uint8_t x49 = Op (Syntax.AddWithGetCarry 24 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x45, Return x24, Return x46);
  { uint32_t x50 = (x29 & 0x7fffff);
  { uint32_t x52, uint8_t _ = Op (Syntax.AddWithGetCarry 23 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x49, Return x27, Return x50);
  out[0] = x32;
  out[1] = x36;
  out[2] = x40;
  out[3] = x44;
  out[4] = x48;
  out[5] = x52;
  }}}}}}}}}}}}}}}}}}}}}}}}}
}
