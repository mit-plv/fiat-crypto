static void freeze(uint64_t out[11], const uint64_t in1[11]) {
  { const uint64_t x19 = in1[10];
  { const uint64_t x20 = in1[9];
  { const uint64_t x18 = in1[8];
  { const uint64_t x16 = in1[7];
  { const uint64_t x14 = in1[6];
  { const uint64_t x12 = in1[5];
  { const uint64_t x10 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint64_t x22, uint8_t x23 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x2, Const 140737488354759);
  { uint64_t x25, uint8_t x26 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x23, Return x4, 0x7fffffffffff);
  { uint64_t x28, uint8_t x29 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x26, Return x6, 0x3fffffffffff);
  { uint64_t x31, uint8_t x32 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x29, Return x8, 0x7fffffffffff);
  { uint64_t x34, uint8_t x35 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x32, Return x10, 0x3fffffffffff);
  { uint64_t x37, uint8_t x38 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x35, Return x12, 0x7fffffffffff);
  { uint64_t x40, uint8_t x41 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x38, Return x14, 0x3fffffffffff);
  { uint64_t x43, uint8_t x44 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x41, Return x16, 0x7fffffffffff);
  { uint64_t x46, uint8_t x47 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x44, Return x18, 0x3fffffffffff);
  { uint64_t x49, uint8_t x50 = Op (Syntax.SubWithGetBorrow 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x47, Return x20, 0x7fffffffffff);
  { uint64_t x52, uint8_t x53 = Op (Syntax.SubWithGetBorrow 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x50, Return x19, 0x3fffffffffff);
  { uint64_t x54 = cmovznz64(x53, 0x0, 0xffffffffffffffffL);
  { uint64_t x55 = (x54 & Const 140737488354759);
  { uint64_t x57, uint8_t x58 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (0x0, Return x22, Return x55);
  { uint64_t x59 = (x54 & 0x7fffffffffff);
  { uint64_t x61, uint8_t x62 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x58, Return x25, Return x59);
  { uint64_t x63 = (x54 & 0x3fffffffffff);
  { uint64_t x65, uint8_t x66 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x62, Return x28, Return x63);
  { uint64_t x67 = (x54 & 0x7fffffffffff);
  { uint64_t x69, uint8_t x70 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x66, Return x31, Return x67);
  { uint64_t x71 = (x54 & 0x3fffffffffff);
  { uint64_t x73, uint8_t x74 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x70, Return x34, Return x71);
  { uint64_t x75 = (x54 & 0x7fffffffffff);
  { uint64_t x77, uint8_t x78 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x74, Return x37, Return x75);
  { uint64_t x79 = (x54 & 0x3fffffffffff);
  { uint64_t x81, uint8_t x82 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x78, Return x40, Return x79);
  { uint64_t x83 = (x54 & 0x7fffffffffff);
  { uint64_t x85, uint8_t x86 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x82, Return x43, Return x83);
  { uint64_t x87 = (x54 & 0x3fffffffffff);
  { uint64_t x89, uint8_t x90 = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x86, Return x46, Return x87);
  { uint64_t x91 = (x54 & 0x7fffffffffff);
  { uint64_t x93, uint8_t x94 = Op (Syntax.AddWithGetCarry 47 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x90, Return x49, Return x91);
  { uint64_t x95 = (x54 & 0x3fffffffffff);
  { uint64_t x97, uint8_t _ = Op (Syntax.AddWithGetCarry 46 (Syntax.TWord 3) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 6) (Syntax.TWord 3)) (Return x94, Return x52, Return x95);
  out[0] = x57;
  out[1] = x61;
  out[2] = x65;
  out[3] = x69;
  out[4] = x73;
  out[5] = x77;
  out[6] = x81;
  out[7] = x85;
  out[8] = x89;
  out[9] = x93;
  out[10] = x97;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
