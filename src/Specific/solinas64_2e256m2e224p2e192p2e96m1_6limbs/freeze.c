static void freeze(uint64_t out[6], const uint64_t in1[6]) {
  { const uint64_t x9 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x12, uint8_t x13 = Op (Syntax.SubWithGetBorrow 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, 0x7ffffffffff);
  { uint64_t x15, uint8_t x16 = Op (Syntax.SubWithGetBorrow 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x13, Return x4, 0x7ffffffffff);
  { uint64_t x18, ℤ x19 = Op (Syntax.SubWithGetBorrow 42 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) Syntax.TZ) (Return x16, Return x6, 0x3ff);
  { uint64_t x21, ℤ x22 = Op (Syntax.SubWithGetBorrow 43 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) Syntax.TZ) (Return x19, Return x8, 0x0);
  { uint64_t x24, ℤ x25 = Op (Syntax.SubWithGetBorrow 43 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) Syntax.TZ) (Return x22, Return x10, 0x200000);
  { uint64_t x27, uint8_t x28 = Op (Syntax.SubWithGetBorrow 42 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x25, Return x9, Const 4398046510080);
  { uint64_t x29 = cmovznz64(x28, 0x0, 0xffffffffffffffffL);
  { uint64_t x30 = (x29 & 0x7ffffffffff);
  { uint64_t x32, uint8_t x33 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x12, Return x30);
  { uint64_t x34 = (x29 & 0x7ffffffffff);
  { uint64_t x36, uint8_t x37 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x33, Return x15, Return x34);
  { uint64_t x38 = (x29 & 0x3ff);
  { uint64_t x40, uint8_t x41 = Op (Syntax.AddWithGetCarry 42 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x37, Return x18, Return x38);
  { uint64_t x43, uint8_t x44 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x41, Return x21, 0x0);
  { uint64_t x45 = (x29 & 0x200000);
  { uint64_t x47, uint8_t x48 = Op (Syntax.AddWithGetCarry 43 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x44, Return x24, Return x45);
  { uint64_t x49 = (x29 & Const 4398046510080);
  { uint64_t x51, uint8_t _ = Op (Syntax.AddWithGetCarry 42 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x48, Return x27, Return x49);
  out[0] = x32;
  out[1] = x36;
  out[2] = x40;
  out[3] = x43;
  out[4] = x47;
  out[5] = x51;
  }}}}}}}}}}}}}}}}}}}}}}}}
}
