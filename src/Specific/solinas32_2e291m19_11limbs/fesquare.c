static void fesquare(uint32_t out[11], const uint32_t in1[11]) {
  { const uint32_t x19 = in1[10];
  { const uint32_t x20 = in1[9];
  { const uint32_t x18 = in1[8];
  { const uint32_t x16 = in1[7];
  { const uint32_t x14 = in1[6];
  { const uint32_t x12 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint64_t x21 = (((uint64_t)x2 * x19) + ((0x2 * ((uint64_t)x4 * x20)) + (((uint64_t)x6 * x18) + ((0x2 * ((uint64_t)x8 * x16)) + (((uint64_t)x10 * x14) + ((0x2 * ((uint64_t)x12 * x12)) + (((uint64_t)x14 * x10) + ((0x2 * ((uint64_t)x16 * x8)) + (((uint64_t)x18 * x6) + ((0x2 * ((uint64_t)x20 * x4)) + ((uint64_t)x19 * x2)))))))))));
  { uint64_t x22 = ((((uint64_t)x2 * x20) + (((uint64_t)x4 * x18) + (((uint64_t)x6 * x16) + (((uint64_t)x8 * x14) + (((uint64_t)x10 * x12) + (((uint64_t)x12 * x10) + (((uint64_t)x14 * x8) + (((uint64_t)x16 * x6) + (((uint64_t)x18 * x4) + ((uint64_t)x20 * x2)))))))))) + (0x13 * ((uint64_t)x19 * x19)));
  { uint64_t x23 = ((((uint64_t)x2 * x18) + ((0x2 * ((uint64_t)x4 * x16)) + (((uint64_t)x6 * x14) + ((0x2 * ((uint64_t)x8 * x12)) + (((uint64_t)x10 * x10) + ((0x2 * ((uint64_t)x12 * x8)) + (((uint64_t)x14 * x6) + ((0x2 * ((uint64_t)x16 * x4)) + ((uint64_t)x18 * x2))))))))) + (0x13 * ((0x2 * ((uint64_t)x20 * x19)) + (0x2 * ((uint64_t)x19 * x20)))));
  { uint64_t x24 = ((((uint64_t)x2 * x16) + (((uint64_t)x4 * x14) + (((uint64_t)x6 * x12) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + (((uint64_t)x12 * x6) + (((uint64_t)x14 * x4) + ((uint64_t)x16 * x2)))))))) + (0x13 * (((uint64_t)x18 * x19) + ((0x2 * ((uint64_t)x20 * x20)) + ((uint64_t)x19 * x18)))));
  { uint64_t x25 = ((((uint64_t)x2 * x14) + ((0x2 * ((uint64_t)x4 * x12)) + (((uint64_t)x6 * x10) + ((0x2 * ((uint64_t)x8 * x8)) + (((uint64_t)x10 * x6) + ((0x2 * ((uint64_t)x12 * x4)) + ((uint64_t)x14 * x2))))))) + (0x13 * ((0x2 * ((uint64_t)x16 * x19)) + ((0x2 * ((uint64_t)x18 * x20)) + ((0x2 * ((uint64_t)x20 * x18)) + (0x2 * ((uint64_t)x19 * x16)))))));
  { uint64_t x26 = ((((uint64_t)x2 * x12) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x12 * x2)))))) + (0x13 * (((uint64_t)x14 * x19) + ((0x2 * ((uint64_t)x16 * x20)) + (((uint64_t)x18 * x18) + ((0x2 * ((uint64_t)x20 * x16)) + ((uint64_t)x19 * x14)))))));
  { ℤ x27 = ((((uint64_t)x2 * x10) + ((0x2 * ((uint64_t)x4 * x8)) + (((uint64_t)x6 * x6) + ((0x2 * ((uint64_t)x8 * x4)) + ((uint64_t)x10 * x2))))) +ℤ (0x13 *ℤ ((0x2 * ((uint64_t)x12 * x19)) + ((0x2 * ((uint64_t)x14 * x20)) + ((0x2 * ((uint64_t)x16 * x18)) + ((0x2 * ((uint64_t)x18 * x16)) + ((0x2 * ((uint64_t)x20 * x14)) + (0x2 * ((uint64_t)x19 * x12)))))))));
  { uint64_t x28 = ((((uint64_t)x2 * x8) + (((uint64_t)x4 * x6) + (((uint64_t)x6 * x4) + ((uint64_t)x8 * x2)))) + (0x13 * (((uint64_t)x10 * x19) + ((0x2 * ((uint64_t)x12 * x20)) + (((uint64_t)x14 * x18) + ((0x2 * ((uint64_t)x16 * x16)) + (((uint64_t)x18 * x14) + ((0x2 * ((uint64_t)x20 * x12)) + ((uint64_t)x19 * x10)))))))));
  { ℤ x29 = ((((uint64_t)x2 * x6) + ((0x2 * ((uint64_t)x4 * x4)) + ((uint64_t)x6 * x2))) +ℤ (0x13 *ℤ ((0x2 * ((uint64_t)x8 * x19)) + ((0x2 * ((uint64_t)x10 * x20)) + ((0x2 * ((uint64_t)x12 * x18)) + ((0x2 * ((uint64_t)x14 * x16)) + ((0x2 * ((uint64_t)x16 * x14)) + ((0x2 * ((uint64_t)x18 * x12)) + ((0x2 * ((uint64_t)x20 * x10)) + (0x2 * ((uint64_t)x19 * x8)))))))))));
  { ℤ x30 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) +ℤ (0x13 *ℤ (((uint64_t)x6 * x19) + ((0x2 * ((uint64_t)x8 * x20)) + (((uint64_t)x10 * x18) + ((0x2 * ((uint64_t)x12 * x16)) + (((uint64_t)x14 * x14) + ((0x2 * ((uint64_t)x16 * x12)) + (((uint64_t)x18 * x10) + ((0x2 * ((uint64_t)x20 * x8)) + ((uint64_t)x19 * x6)))))))))));
  { ℤ x31 = (((uint64_t)x2 * x2) +ℤ (0x13 *ℤ ((0x2 * ((uint64_t)x4 * x19)) + ((0x2 * ((uint64_t)x6 * x20)) + ((0x2 * ((uint64_t)x8 * x18)) + ((0x2 * ((uint64_t)x10 * x16)) + ((0x2 * ((uint64_t)x12 * x14)) + ((0x2 * ((uint64_t)x14 * x12)) + ((0x2 * ((uint64_t)x16 * x10)) + ((0x2 * ((uint64_t)x18 * x8)) + ((0x2 * ((uint64_t)x20 * x6)) + (0x2 * ((uint64_t)x19 * x4)))))))))))));
  { uint64_t x32 = (x31 >> 0x1b);
  { uint32_t x33 = (x31 & 0x7ffffff);
  { ℤ x34 = (x32 +ℤ x30);
  { uint64_t x35 = (x34 >> 0x1a);
  { uint32_t x36 = (x34 & 0x3ffffff);
  { ℤ x37 = (x35 +ℤ x29);
  { uint64_t x38 = (x37 >> 0x1b);
  { uint32_t x39 = (x37 & 0x7ffffff);
  { uint64_t x40 = (x38 + x28);
  { uint64_t x41 = (x40 >> 0x1a);
  { uint32_t x42 = ((uint32_t)x40 & 0x3ffffff);
  { ℤ x43 = (x41 +ℤ x27);
  { uint64_t x44 = (x43 >> 0x1b);
  { uint32_t x45 = (x43 & 0x7ffffff);
  { uint64_t x46 = (x44 + x26);
  { uint64_t x47 = (x46 >> 0x1a);
  { uint32_t x48 = ((uint32_t)x46 & 0x3ffffff);
  { uint64_t x49 = (x47 + x25);
  { uint64_t x50 = (x49 >> 0x1b);
  { uint32_t x51 = ((uint32_t)x49 & 0x7ffffff);
  { uint64_t x52 = (x50 + x24);
  { uint64_t x53 = (x52 >> 0x1a);
  { uint32_t x54 = ((uint32_t)x52 & 0x3ffffff);
  { uint64_t x55 = (x53 + x23);
  { uint64_t x56 = (x55 >> 0x1b);
  { uint32_t x57 = ((uint32_t)x55 & 0x7ffffff);
  { uint64_t x58 = (x56 + x22);
  { uint64_t x59 = (x58 >> 0x1a);
  { uint32_t x60 = ((uint32_t)x58 & 0x3ffffff);
  { uint64_t x61 = (x59 + x21);
  { uint64_t x62 = (x61 >> 0x1a);
  { uint32_t x63 = ((uint32_t)x61 & 0x3ffffff);
  { uint64_t x64 = (x33 + (0x13 * x62));
  { uint32_t x65 = (uint32_t) (x64 >> 0x1b);
  { uint32_t x66 = ((uint32_t)x64 & 0x7ffffff);
  { uint32_t x67 = (x65 + x36);
  { uint32_t x68 = (x67 >> 0x1a);
  { uint32_t x69 = (x67 & 0x3ffffff);
  out[0] = x66;
  out[1] = x69;
  out[2] = (x68 + x39);
  out[3] = x42;
  out[4] = x45;
  out[5] = x48;
  out[6] = x51;
  out[7] = x54;
  out[8] = x57;
  out[9] = x60;
  out[10] = x63;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
