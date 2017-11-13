static void freeze(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x10, ℤ x11 = Op (Syntax.SubWithGetBorrow 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) Syntax.TZ) (0x0, Return x2, 0x1);
  { uint64_t x13, ℤ x14 = Op (Syntax.SubWithGetBorrow 45 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) Syntax.TZ) (Return x11, Return x4, 0x0);
  { uint64_t x16, uint8_t x17 = Op (Syntax.SubWithGetBorrow 45 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x14, Return x6, Const 35184372088768);
  { uint64_t x19, uint8_t x20 = Op (Syntax.SubWithGetBorrow 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x17, Return x8, 0x1fffffffffff);
  { uint64_t x22, uint8_t x23 = Op (Syntax.SubWithGetBorrow 44 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x20, Return x7, 0xfffffffffff);
  { uint64_t x24 = cmovznz64(x23, 0x0, 0xffffffffffffffffL);
  { uint8_t x25 = ((uint8_t)x24 & 0x1);
  { uint64_t x27, uint8_t x28 = Op (Syntax.AddWithGetCarry 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x10, Return x25);
  { uint64_t x30, uint8_t x31 = Op (Syntax.AddWithGetCarry 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x28, Return x13, 0x0);
  { uint64_t x32 = (x24 & Const 35184372088768);
  { uint64_t x34, uint8_t x35 = Op (Syntax.AddWithGetCarry 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x31, Return x16, Return x32);
  { uint64_t x36 = (x24 & 0x1fffffffffff);
  { uint64_t x38, uint8_t x39 = Op (Syntax.AddWithGetCarry 45 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x35, Return x19, Return x36);
  { uint64_t x40 = (x24 & 0xfffffffffff);
  { uint64_t x42, uint8_t _ = Op (Syntax.AddWithGetCarry 44 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x39, Return x22, Return x40);
  out[0] = x27;
  out[1] = x30;
  out[2] = x34;
  out[3] = x38;
  out[4] = x42;
  }}}}}}}}}}}}}}}}}}}}
}
