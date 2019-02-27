static void freeze(uint64_t out[6], const uint64_t in1[6]) {
  { const uint64_t x9 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x12, ℤ x13 = Op (Syntax.SubWithGetBorrow 38 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 0) (Syntax.TWord 6) Syntax.TZ) (0x0, Return x2, 0x1);
  { uint64_t x15, ℤ x16 = Op (Syntax.SubWithGetBorrow 37 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 0) (Syntax.TWord 6) Syntax.TZ) (Return x13, Return x4, 0x0);
  { uint64_t x18, uint8_t/*bool*/ x19 = Op (Syntax.SubWithGetBorrow 37 Syntax.TZ (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x16, Return x6, 0x1fffe00000);
  { uint64_t x21, uint8_t/*bool*/ x22 = Op (Syntax.SubWithGetBorrow 38 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x19, Return x8, 0x3fffffffff);
  { uint64_t x24, uint8_t/*bool*/ x25 = Op (Syntax.SubWithGetBorrow 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x22, Return x10, 0x1fffffffff);
  { uint64_t x27, uint8_t/*bool*/ x28 = Op (Syntax.SubWithGetBorrow 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x25, Return x9, 0x1fffffffff);
  { uint64_t x29 = cmovznz64(x28, 0x0, 0xffffffffffffffffL);
  { uint8_t/*bool*/ x30 = (1&(uint8_t/*bool*/)x29 & 0x1);
  { uint64_t x32, uint8_t/*bool*/ x33 = Op (Syntax.AddWithGetCarry 38 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 0)) (0x0, Return x12, Return x30);
  { uint64_t x35, uint8_t/*bool*/ x36 = Op (Syntax.AddWithGetCarry 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x33, Return x15, 0x0);
  { uint64_t x37 = (x29 & 0x1fffe00000);
  { uint64_t x39, uint8_t/*bool*/ x40 = Op (Syntax.AddWithGetCarry 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x36, Return x18, Return x37);
  { uint64_t x41 = (x29 & 0x3fffffffff);
  { uint64_t x43, uint8_t/*bool*/ x44 = Op (Syntax.AddWithGetCarry 38 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x40, Return x21, Return x41);
  { uint64_t x45 = (x29 & 0x1fffffffff);
  { uint64_t x47, uint8_t/*bool*/ x48 = Op (Syntax.AddWithGetCarry 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x44, Return x24, Return x45);
  { uint64_t x49 = (x29 & 0x1fffffffff);
  { uint64_t x51, uint8_t/*bool*/ _ = Op (Syntax.AddWithGetCarry 37 (Syntax.TWord 0) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 0)) (Return x48, Return x27, Return x49);
  out[0] = x32;
  out[1] = x35;
  out[2] = x39;
  out[3] = x43;
  out[4] = x47;
  out[5] = x51;
  }}}}}}}}}}}}}}}}}}}}}}}}
}
