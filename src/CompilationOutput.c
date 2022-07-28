     = ErrorT.Success
         ("/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 *   arg2: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
 */
static FIAT_FIAT_INLINE void bitcoin_mul_u64(uint64_t out1[5], const uint64_t arg1[5], const uint64_t arg2[5]) {
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
  uint64_t x52;
  uint64_t x53;
  uint64_t x54;
  uint64_t x55;
  uint64_t x56;
  uint64_t x57;
  uint64_t x58;
  uint64_t x59;
  uint64_t x60;
  uint64_t x61;
  uint64_t x62;
  uint64_t x63;
  uint64_t x64;
  uint64_t x65;
  uint64_t x66;
  uint64_t x67;
  uint64_t x68;
  uint64_t x69;
  uint64_t x70;
  uint64_t x71;
  uint64_t x72;
  uint64_t x73;
  uint64_t x74;
  uint64_t x75;
  uint64_t x76;
  uint64_t x77;
  uint64_t x78;
  uint64_t x79;
  uint64_t x80;
  uint64_t x81;
  uint64_t x82;
  uint64_t x83;
  uint64_t x84;
  uint64_t x85;
  uint64_t x86;
  uint64_t x87;
  uint64_t x88;
  uint64_t x89;
  uint64_t x90;
  uint64_t x91;
  uint64_t x92;
  uint64_t x93;
  uint64_t x94;
  uint64_t x95;
  uint64_t x96;
  uint64_t x97;
  uint64_t x98;
  uint64_t x99;
  uint64_t x100;
  uint64_t x101;
  uint64_t x102;
  uint64_t x103;
  uint64_t x104;
  uint64_t x105;
  uint64_t x106;
  uint64_t x107;
  uint64_t x108;
  uint64_t x109;
  uint64_t x110;
  uint64_t x111;
  uint64_t x112;
  uint64_t x113;
  uint64_t x114;
  uint64_t x115;
  uint64_t x116;
  uint64_t x117;
  uint64_t x118;
  uint64_t x119;
  uint64_t x120;
  uint64_t x121;
  uint64_t x122;
  uint64_t x123;
  uint64_t x124;
  uint64_t x125;
  uint64_t x126;
  uint64_t x127;
  uint64_t x128;
  uint64_t x129;
  uint64_t x130;
  uint64_t x131;
  uint64_t x132;
  uint64_t x133;
  uint64_t x134;
  uint64_t x135;
  uint64_t x136;
  uint64_t x137;
  uint64_t x138;
  uint64_t x139;
  uint64_t x140;
  uint64_t x141;
  uint64_t x142;
  uint64_t x143;
  uint64_t x144;
  uint64_t x145;
  uint64_t x146;
  uint64_t x147;
  uint64_t x148;
  uint64_t x149;
  uint64_t x150;
  uint64_t x151;
  uint64_t x152;
  uint64_t x153;
  uint64_t x154;
  uint64_t x155;
  uint64_t x156;
  uint64_t x157;
  uint64_t x158;
  uint64_t x159;
  uint64_t x160;
  uint64_t x161;
  uint64_t x162;
  uint64_t x163;
  uint64_t x164;
  uint64_t x165;
  uint64_t x166;
  fiat_mulx_u64(&x1, &x2, (arg1[4]), (arg2[4]));
  fiat_mulx_u64(&x3, &x4, (arg1[0]), (arg2[3]));
  fiat_mulx_u64(&x5, &x6, (arg1[1]), (arg2[2]));
  fiat_mulx_u64(&x7, &x8, (arg1[2]), (arg2[1]));
  fiat_mulx_u64(&x9, &x10, (arg1[3]), (arg2[0]));
  fiat_addcarryx_u64(&x11, &x12, 0x0, x9, x7);
  fiat_addcarryx_u64(&x13, &x14, 0x0, x11, x5);
  fiat_addcarryx_u64(&x15, &x16, 0x0, x13, x3);
  fiat_mulx_u64(&x17, &x18, (x1 & UINT64_C(0xfffffffffffff)), UINT64_C(0x1000003d10));
  fiat_addcarryx_u64(&x19, &x20, 0x0, x17, x15);
  fiat_mulx_u64(&x21, &x22, (arg1[0]), (arg2[4]));
  fiat_mulx_u64(&x23, &x24, (arg1[1]), (arg2[3]));
  fiat_mulx_u64(&x25, &x26, (arg1[2]), (arg2[2]));
  fiat_mulx_u64(&x27, &x28, (arg1[3]), (arg2[1]));
  fiat_mulx_u64(&x29, &x30, (arg1[4]), (arg2[0]));
  fiat_addcarryx_u64(&x31, &x32, 0x0, x29, x27);
  fiat_addcarryx_u64(&x33, &x34, 0x0, x31, x25);
  fiat_addcarryx_u64(&x35, &x36, 0x0, x33, x23);
  fiat_addcarryx_u64(&x37, &x38, 0x0, x35, x21);
  fiat_addcarryx_u64(&x39, &x40, x12, x10, x8);
  fiat_addcarryx_u64(&x41, &x42, x14, x39, x6);
  fiat_addcarryx_u64(&x43, &x44, x16, x41, x4);
  fiat_addcarryx_u64(&x45, &x46, x20, x18, x43);
  fiat_addcarryx_u64(&x47, &x48, 0x0, ((x19 >> 52) | ((x45 << 12) & UINT64_C(0xffffffffffffffff))), x37);
  fiat_mulx_u64(&x49, &x50, ((x1 >> 52) | ((x2 << 12) & UINT64_C(0xffffffffffffffff))), UINT64_C(0x1000003d10));
  fiat_addcarryx_u64(&x51, &x52, 0x0, x49, x47);
  x53 = (x51 & UINT64_C(0xfffffffffffff));
  fiat_mulx_u64(&x54, &x55, (arg1[1]), (arg2[4]));
  fiat_mulx_u64(&x56, &x57, (arg1[2]), (arg2[3]));
  fiat_mulx_u64(&x58, &x59, (arg1[3]), (arg2[2]));
  fiat_mulx_u64(&x60, &x61, (arg1[4]), (arg2[1]));
  fiat_addcarryx_u64(&x62, &x63, 0x0, x60, x58);
  fiat_addcarryx_u64(&x64, &x65, 0x0, x62, x56);
  fiat_addcarryx_u64(&x66, &x67, 0x0, x64, x54);
  fiat_addcarryx_u64(&x68, &x69, x32, x30, x28);
  fiat_addcarryx_u64(&x70, &x71, x34, x68, x26);
  fiat_addcarryx_u64(&x72, &x73, x36, x70, x24);
  fiat_addcarryx_u64(&x74, &x75, x38, x72, x22);
  fiat_addcarryx_u64(&x76, &x77, x52, x50, (x48 + x74));
  fiat_addcarryx_u64(&x78, &x79, 0x0, ((x51 >> 52) | ((x76 << 12) & UINT64_C(0xffffffffffffffff))), x66);
  fiat_mulx_u64(&x80, &x81, (arg1[0]), (arg2[0]));
  fiat_mulx_u64(&x82, &x83, ((x53 >> 48) + ((x78 & UINT64_C(0xfffffffffffff)) << 4)), UINT64_C(0x1000003d1));
  fiat_addcarryx_u64(&x84, &x85, 0x0, x82, x80);
  fiat_mulx_u64(&x86, &x87, (arg1[2]), (arg2[4]));
  fiat_mulx_u64(&x88, &x89, (arg1[3]), (arg2[3]));
  fiat_mulx_u64(&x90, &x91, (arg1[4]), (arg2[2]));
  fiat_addcarryx_u64(&x92, &x93, 0x0, x90, x88);
  fiat_addcarryx_u64(&x94, &x95, 0x0, x92, x86);
  fiat_addcarryx_u64(&x96, &x97, x63, x61, x59);
  fiat_addcarryx_u64(&x98, &x99, x65, x96, x57);
  fiat_addcarryx_u64(&x100, &x101, x67, x98, x55);
  fiat_addcarryx_u64(&x102, &x103, 0x0, ((x78 >> 52) | (((x79 + x100) << 12) & UINT64_C(0xffffffffffffffff))), x94);
  fiat_mulx_u64(&x104, &x105, (arg1[0]), (arg2[1]));
  fiat_mulx_u64(&x106, &x107, (arg1[1]), (arg2[0]));
  fiat_addcarryx_u64(&x108, &x109, 0x0, x106, x104);
  fiat_addcarryx_u64(&x110, &x111, x85, x83, x81);
  fiat_addcarryx_u64(&x112, &x113, 0x0, ((x84 >> 52) | ((x110 << 12) & UINT64_C(0xffffffffffffffff))), x108);
  fiat_mulx_u64(&x114, &x115, (x102 & UINT64_C(0xfffffffffffff)), UINT64_C(0x1000003d10));
  fiat_addcarryx_u64(&x116, &x117, 0x0, x114, x112);
  fiat_mulx_u64(&x118, &x119, (arg1[3]), (arg2[4]));
  fiat_mulx_u64(&x120, &x121, (arg1[4]), (arg2[3]));
  fiat_addcarryx_u64(&x122, &x123, 0x0, x120, x118);
  fiat_addcarryx_u64(&x124, &x125, x93, x91, x89);
  fiat_addcarryx_u64(&x126, &x127, x95, x124, x87);
  fiat_addcarryx_u64(&x128, &x129, 0x0, ((x102 >> 52) | (((x103 + x126) << 12) & UINT64_C(0xffffffffffffffff))), x122);
  fiat_mulx_u64(&x130, &x131, (arg1[0]), (arg2[2]));
  fiat_mulx_u64(&x132, &x133, (arg1[1]), (arg2[1]));
  fiat_mulx_u64(&x134, &x135, (arg1[2]), (arg2[0]));
  fiat_addcarryx_u64(&x136, &x137, 0x0, x134, x132);
  fiat_addcarryx_u64(&x138, &x139, 0x0, x136, x130);
  fiat_addcarryx_u64(&x140, &x141, x109, x107, x105);
  fiat_addcarryx_u64(&x142, &x143, x117, x115, (x113 + x140));
  fiat_addcarryx_u64(&x144, &x145, 0x0, ((x116 >> 52) | ((x142 << 12) & UINT64_C(0xffffffffffffffff))), x138);
  fiat_mulx_u64(&x146, &x147, (x128 & UINT64_C(0xfffffffffffff)), UINT64_C(0x1000003d10));
  fiat_addcarryx_u64(&x148, &x149, 0x0, x146, x144);
  fiat_addcarryx_u64(&x150, &x151, x123, x121, x119);
  fiat_mulx_u64(&x152, &x153, ((x128 >> 52) | (((x129 + x150) << 12) & UINT64_C(0xffffffffffffffff))), UINT64_C(0x1000003d10));
  fiat_addcarryx_u64(&x154, &x155, x137, x135, x133);
  fiat_addcarryx_u64(&x156, &x157, x139, x154, x131);
  fiat_addcarryx_u64(&x158, &x159, x149, x147, (x145 + x156));
  fiat_addcarryx_u64(&x160, &x161, 0x0, x152, (((x148 >> 52) | ((x158 << 12) & UINT64_C(0xffffffffffffffff))) + (x19 & UINT64_C(0xfffffffffffff))));
  x162 = (x84 & UINT64_C(0xfffffffffffff));
  x163 = (x116 & UINT64_C(0xfffffffffffff));
  x164 = (x148 & UINT64_C(0xfffffffffffff));
  x165 = (x160 & UINT64_C(0xfffffffffffff));
  x166 = (((x160 >> 52) | (((x161 + x153) << 12) & UINT64_C(0xffffffffffffffff))) + (x53 & UINT64_C(0xffffffffffff)));
  out1[0] = x162;
  out1[1] = x163;
  out1[2] = x164;
  out1[3] = x165;
  out1[4] = x166;
}"%string,
         {|
           ToString.bitwidths_used :=
             (MSetPositive.PositiveSet.Leaf,
             MSetPositive.PositiveSet.Node MSetPositive.PositiveSet.Leaf false
               (MSetPositive.PositiveSet.Node MSetPositive.PositiveSet.Leaf false
                  (MSetPositive.PositiveSet.Node MSetPositive.PositiveSet.Leaf true
                     MSetPositive.PositiveSet.Leaf)));
           ToString.addcarryx_lg_splits :=
             MSetPositive.PositiveSet.Node
               (MSetPositive.PositiveSet.Node
                  (MSetPositive.PositiveSet.Node
                     (MSetPositive.PositiveSet.Node
                        (MSetPositive.PositiveSet.Node
                           (MSetPositive.PositiveSet.Node
                              (MSetPositive.PositiveSet.Node MSetPositive.PositiveSet.Leaf
                                 true MSetPositive.PositiveSet.Leaf) false
                              MSetPositive.PositiveSet.Leaf) false
                           MSetPositive.PositiveSet.Leaf) false MSetPositive.PositiveSet.Leaf)
                     false MSetPositive.PositiveSet.Leaf) false MSetPositive.PositiveSet.Leaf)
               false MSetPositive.PositiveSet.Leaf;
           ToString.mulx_lg_splits :=
             MSetPositive.PositiveSet.Node
               (MSetPositive.PositiveSet.Node
                  (MSetPositive.PositiveSet.Node
                     (MSetPositive.PositiveSet.Node
                        (MSetPositive.PositiveSet.Node
                           (MSetPositive.PositiveSet.Node
                              (MSetPositive.PositiveSet.Node MSetPositive.PositiveSet.Leaf
                                 true MSetPositive.PositiveSet.Leaf) false
                              MSetPositive.PositiveSet.Leaf) false
                           MSetPositive.PositiveSet.Leaf) false MSetPositive.PositiveSet.Leaf)
                     false MSetPositive.PositiveSet.Leaf) false MSetPositive.PositiveSet.Leaf)
               false MSetPositive.PositiveSet.Leaf;
           ToString.cmovznz_bitwidths :=
             (MSetPositive.PositiveSet.Leaf, MSetPositive.PositiveSet.Leaf);
           ToString.value_barrier_bitwidths :=
             (MSetPositive.PositiveSet.Leaf, MSetPositive.PositiveSet.Leaf);
           ToString.typedefs_used := []
         |})
     : Pipeline.ErrorT (string * ToString.ident_infos)
Finished transaction in 7.921 secs (7.896u,0.033s) (successful)
