/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */

static NATHANTEST_FIAT_INLINE void nathantest_manually_looped_redc_25519(uint64_t out1[4], const uint64_t arg1[4], const uint64_t arg2[7], const uint64_t arg3[4]){
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  uint64_t x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  uint64_t x15;
  uint64_t x16;
  uint64_t x17;
  uint64_t x18;
  uint64_t x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  uint64_t x32;
  uint64_t x33;
  uint64_t x34;
  uint64_t x35;
  uint64_t x36;
  uint64_t x37;
  uint64_t x38;
  uint64_t x39;
  uint64_t x40;
  uint64_t x41;
  uint64_t x42;
  uint64_t x43;
  uint64_t x44;
  uint64_t x45;
  uint64_t x46;
  uint64_t x47;
  uint64_t x48;
  uint64_t x49;
  uint64_t x50;
  uint64_t x51;

  x48 = (arg1[0]);
  x49 = (arg1[1]);
  x50 = (arg1[2]);
  x51 = (arg1[3]);
  
  for (int i = 0; i<3; i = i + 1) {
    x1 = (arg2[i]);
    nathantest_mulx_u64(&x2, &x3, x1, (arg3[2])); 
    nathantest_mulx_u64(&x4, &x5, x1, (arg3[1]));
    nathantest_mulx_u64(&x6, &x7, x1, (arg3[0]));
    nathantest_addcarryx_u64(&x8, &x9, 0x0, x7, x4);
    nathantest_addcarryx_u64(&x10, &x11, x9, x5, x2);
    nathantest_addcarryx_u64(&x12, &x13, 0x0, (x48 /* arg1[0] */ ), x6);
    nathantest_addcarryx_u64(&x14, &x15, x13, (x49 /* arg1[1] */ ), x8);
    nathantest_addcarryx_u64(&x16, &x17, x15, (x50 /* arg1[2] */), x10);
    nathantest_mulx_u64(&x18, &x19, x1, (arg3[3]));
    nathantest_addcarryx_u64(&x20, &x21, x11, x3, x18);
    nathantest_addcarryx_u64(&x22, &x23, x17, (x51 /* arg1[3] */), x20);
    nathantest_mulx_u64(&x24, &x25, x12, UINT64_C(0x86bca1af286bca1b));
    nathantest_mulx_u64(&x26, &x27, x24, UINT64_C(0x7fffffffffffffff));
    nathantest_mulx_u64(&x28, &x29, x24, UINT64_C(0xffffffffffffffff));
    nathantest_mulx_u64(&x30, &x31, x24, UINT64_C(0xffffffffffffffff));
    nathantest_mulx_u64(&x32, &x33, x24, UINT64_C(0xffffffffffffffed));
    nathantest_addcarryx_u64(&x34, &x35, 0x0, x33, x30);
    nathantest_addcarryx_u64(&x36, &x37, x35, x31, x28);
    nathantest_addcarryx_u64(&x38, &x39, x37, x29, x26);
    nathantest_addcarryx_u64(&x40, &x41, 0x0, x12, x32);
    nathantest_addcarryx_u64(&x42, &x43, x41, x14, x34);
    nathantest_addcarryx_u64(&x44, &x45, x43, x16, x36);
    nathantest_addcarryx_u64(&x46, &x47, x45, x22, x38);
    x48 = x42;
    x49 = x44;
    x50 = x46;
    x51 = ((x47 + x23) + (x39 + x27));
  }
  
  out1[0] = x48;
  out1[1] = x49;
  out1[2] = x50;
  out1[3] = x51;
  
}
