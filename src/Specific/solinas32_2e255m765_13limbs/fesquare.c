static void fesquare(uint32_t out[13], const uint32_t in1[13]) {
  { const uint32_t x23 = in1[12];
  { const uint32_t x24 = in1[11];
  { const uint32_t x22 = in1[10];
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
  { uint64_t x25 = (((uint64_t)x2 * x23) + (((uint64_t)x4 * x24) + ((0x2 * ((uint64_t)x6 * x22)) + (((uint64_t)x8 * x20) + (((uint64_t)x10 * x18) + ((0x2 * ((uint64_t)x12 * x16)) + (((uint64_t)x14 * x14) + ((0x2 * ((uint64_t)x16 * x12)) + (((uint64_t)x18 * x10) + (((uint64_t)x20 * x8) + ((0x2 * ((uint64_t)x22 * x6)) + (((uint64_t)x24 * x4) + ((uint64_t)x23 * x2)))))))))))));
  { uint64_t x26 = ((((uint64_t)x2 * x24) + ((0x2 * ((uint64_t)x4 * x22)) + ((0x2 * ((uint64_t)x6 * x20)) + (((uint64_t)x8 * x18) + ((0x2 * ((uint64_t)x10 * x16)) + ((0x2 * ((uint64_t)x12 * x14)) + ((0x2 * ((uint64_t)x14 * x12)) + ((0x2 * ((uint64_t)x16 * x10)) + (((uint64_t)x18 * x8) + ((0x2 * ((uint64_t)x20 * x6)) + ((0x2 * ((uint64_t)x22 * x4)) + ((uint64_t)x24 * x2)))))))))))) + (0x2fd * (0x2 * ((uint64_t)x23 * x23))));
  { uint64_t x27 = ((((uint64_t)x2 * x22) + (((uint64_t)x4 * x20) + (((uint64_t)x6 * x18) + (((uint64_t)x8 * x16) + (((uint64_t)x10 * x14) + ((0x2 * ((uint64_t)x12 * x12)) + (((uint64_t)x14 * x10) + (((uint64_t)x16 * x8) + (((uint64_t)x18 * x6) + (((uint64_t)x20 * x4) + ((uint64_t)x22 * x2))))))))))) + (0x2fd * (((uint64_t)x24 * x23) + ((uint64_t)x23 * x24))));
  { uint64_t x28 = ((((uint64_t)x2 * x20) + (((uint64_t)x4 * x18) + ((0x2 * ((uint64_t)x6 * x16)) + (((uint64_t)x8 * x14) + ((0x2 * ((uint64_t)x10 * x12)) + ((0x2 * ((uint64_t)x12 * x10)) + (((uint64_t)x14 * x8) + ((0x2 * ((uint64_t)x16 * x6)) + (((uint64_t)x18 * x4) + ((uint64_t)x20 * x2)))))))))) + (0x2fd * ((0x2 * ((uint64_t)x22 * x23)) + (((uint64_t)x24 * x24) + (0x2 * ((uint64_t)x23 * x22))))));
  { uint64_t x29 = ((((uint64_t)x2 * x18) + ((0x2 * ((uint64_t)x4 * x16)) + ((0x2 * ((uint64_t)x6 * x14)) + ((0x2 * ((uint64_t)x8 * x12)) + ((0x2 * ((uint64_t)x10 * x10)) + ((0x2 * ((uint64_t)x12 * x8)) + ((0x2 * ((uint64_t)x14 * x6)) + ((0x2 * ((uint64_t)x16 * x4)) + ((uint64_t)x18 * x2))))))))) + (0x2fd * ((0x2 * ((uint64_t)x20 * x23)) + ((0x2 * ((uint64_t)x22 * x24)) + ((0x2 * ((uint64_t)x24 * x22)) + (0x2 * ((uint64_t)x23 * x20)))))));
  { uint64_t x30 = ((((uint64_t)x2 * x16) + (((uint64_t)x4 * x14) + ((0x2 * ((uint64_t)x6 * x12)) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + ((0x2 * ((uint64_t)x12 * x6)) + (((uint64_t)x14 * x4) + ((uint64_t)x16 * x2)))))))) + (0x2fd * (((uint64_t)x18 * x23) + (((uint64_t)x20 * x24) + ((0x2 * ((uint64_t)x22 * x22)) + (((uint64_t)x24 * x20) + ((uint64_t)x23 * x18)))))));
  { uint64_t x31 = ((((uint64_t)x2 * x14) + ((0x2 * ((uint64_t)x4 * x12)) + ((0x2 * ((uint64_t)x6 * x10)) + (((uint64_t)x8 * x8) + ((0x2 * ((uint64_t)x10 * x6)) + ((0x2 * ((uint64_t)x12 * x4)) + ((uint64_t)x14 * x2))))))) + (0x2fd * ((0x2 * ((uint64_t)x16 * x23)) + (((uint64_t)x18 * x24) + ((0x2 * ((uint64_t)x20 * x22)) + ((0x2 * ((uint64_t)x22 * x20)) + (((uint64_t)x24 * x18) + (0x2 * ((uint64_t)x23 * x16)))))))));
  { uint64_t x32 = ((((uint64_t)x2 * x12) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x12 * x2)))))) + (0x2fd * (((uint64_t)x14 * x23) + (((uint64_t)x16 * x24) + (((uint64_t)x18 * x22) + (((uint64_t)x20 * x20) + (((uint64_t)x22 * x18) + (((uint64_t)x24 * x16) + ((uint64_t)x23 * x14)))))))));
  { uint64_t x33 = ((((uint64_t)x2 * x10) + (((uint64_t)x4 * x8) + ((0x2 * ((uint64_t)x6 * x6)) + (((uint64_t)x8 * x4) + ((uint64_t)x10 * x2))))) + (0x2fd * ((0x2 * ((uint64_t)x12 * x23)) + (((uint64_t)x14 * x24) + ((0x2 * ((uint64_t)x16 * x22)) + (((uint64_t)x18 * x20) + (((uint64_t)x20 * x18) + ((0x2 * ((uint64_t)x22 * x16)) + (((uint64_t)x24 * x14) + (0x2 * ((uint64_t)x23 * x12)))))))))));
  { uint64_t x34 = ((((uint64_t)x2 * x8) + ((0x2 * ((uint64_t)x4 * x6)) + ((0x2 * ((uint64_t)x6 * x4)) + ((uint64_t)x8 * x2)))) + (0x2fd * ((0x2 * ((uint64_t)x10 * x23)) + ((0x2 * ((uint64_t)x12 * x24)) + ((0x2 * ((uint64_t)x14 * x22)) + ((0x2 * ((uint64_t)x16 * x20)) + (((uint64_t)x18 * x18) + ((0x2 * ((uint64_t)x20 * x16)) + ((0x2 * ((uint64_t)x22 * x14)) + ((0x2 * ((uint64_t)x24 * x12)) + (0x2 * ((uint64_t)x23 * x10))))))))))));
  { uint64_t x35 = ((((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))) + (0x2fd * (((uint64_t)x8 * x23) + (((uint64_t)x10 * x24) + ((0x2 * ((uint64_t)x12 * x22)) + (((uint64_t)x14 * x20) + (((uint64_t)x16 * x18) + (((uint64_t)x18 * x16) + (((uint64_t)x20 * x14) + ((0x2 * ((uint64_t)x22 * x12)) + (((uint64_t)x24 * x10) + ((uint64_t)x23 * x8))))))))))));
  { uint64_t x36 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (0x2fd * ((0x2 * ((uint64_t)x6 * x23)) + (((uint64_t)x8 * x24) + ((0x2 * ((uint64_t)x10 * x22)) + ((0x2 * ((uint64_t)x12 * x20)) + (((uint64_t)x14 * x18) + ((0x2 * ((uint64_t)x16 * x16)) + (((uint64_t)x18 * x14) + ((0x2 * ((uint64_t)x20 * x12)) + ((0x2 * ((uint64_t)x22 * x10)) + (((uint64_t)x24 * x8) + (0x2 * ((uint64_t)x23 * x6))))))))))))));
  { uint64_t x37 = (((uint64_t)x2 * x2) + (0x2fd * ((0x2 * ((uint64_t)x4 * x23)) + ((0x2 * ((uint64_t)x6 * x24)) + ((0x2 * ((uint64_t)x8 * x22)) + ((0x2 * ((uint64_t)x10 * x20)) + ((0x2 * ((uint64_t)x12 * x18)) + ((0x2 * ((uint64_t)x14 * x16)) + ((0x2 * ((uint64_t)x16 * x14)) + ((0x2 * ((uint64_t)x18 * x12)) + ((0x2 * ((uint64_t)x20 * x10)) + ((0x2 * ((uint64_t)x22 * x8)) + ((0x2 * ((uint64_t)x24 * x6)) + (0x2 * ((uint64_t)x23 * x4)))))))))))))));
  { uint64_t x38 = (x37 >> 0x14);
  { uint32_t x39 = ((uint32_t)x37 & 0xfffff);
  { uint64_t x40 = (x38 + x36);
  { uint64_t x41 = (x40 >> 0x14);
  { uint32_t x42 = ((uint32_t)x40 & 0xfffff);
  { uint64_t x43 = (x41 + x35);
  { uint64_t x44 = (x43 >> 0x13);
  { uint32_t x45 = ((uint32_t)x43 & 0x7ffff);
  { uint64_t x46 = (x44 + x34);
  { uint64_t x47 = (x46 >> 0x14);
  { uint32_t x48 = ((uint32_t)x46 & 0xfffff);
  { uint64_t x49 = (x47 + x33);
  { uint64_t x50 = (x49 >> 0x14);
  { uint32_t x51 = ((uint32_t)x49 & 0xfffff);
  { uint64_t x52 = (x50 + x32);
  { uint64_t x53 = (x52 >> 0x13);
  { uint32_t x54 = ((uint32_t)x52 & 0x7ffff);
  { uint64_t x55 = (x53 + x31);
  { uint64_t x56 = (x55 >> 0x14);
  { uint32_t x57 = ((uint32_t)x55 & 0xfffff);
  { uint64_t x58 = (x56 + x30);
  { uint64_t x59 = (x58 >> 0x13);
  { uint32_t x60 = ((uint32_t)x58 & 0x7ffff);
  { uint64_t x61 = (x59 + x29);
  { uint64_t x62 = (x61 >> 0x14);
  { uint32_t x63 = ((uint32_t)x61 & 0xfffff);
  { uint64_t x64 = (x62 + x28);
  { uint64_t x65 = (x64 >> 0x14);
  { uint32_t x66 = ((uint32_t)x64 & 0xfffff);
  { uint64_t x67 = (x65 + x27);
  { uint64_t x68 = (x67 >> 0x13);
  { uint32_t x69 = ((uint32_t)x67 & 0x7ffff);
  { uint64_t x70 = (x68 + x26);
  { uint64_t x71 = (x70 >> 0x14);
  { uint32_t x72 = ((uint32_t)x70 & 0xfffff);
  { uint64_t x73 = (x71 + x25);
  { uint32_t x74 = (uint32_t) (x73 >> 0x13);
  { uint32_t x75 = ((uint32_t)x73 & 0x7ffff);
  { uint64_t x76 = (x39 + ((uint64_t)0x2fd * x74));
  { uint32_t x77 = (uint32_t) (x76 >> 0x14);
  { uint32_t x78 = ((uint32_t)x76 & 0xfffff);
  { uint32_t x79 = (x77 + x42);
  { uint32_t x80 = (x79 >> 0x14);
  { uint32_t x81 = (x79 & 0xfffff);
  out[0] = x78;
  out[1] = x81;
  out[2] = (x80 + x45);
  out[3] = x48;
  out[4] = x51;
  out[5] = x54;
  out[6] = x57;
  out[7] = x60;
  out[8] = x63;
  out[9] = x66;
  out[10] = x69;
  out[11] = x72;
  out[12] = x75;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
