// Code generated by Fiat Cryptography. DO NOT EDIT.
//
// Autogenerated: 'src/ExtractionOCaml/dettman_multiplication' --lang Go --no-wide-int --relax-primitive-carry-to-bitwidth 32,64 --cmovznz-by-mul --internal-static --package-case flatcase --public-function-case UpperCamelCase --private-function-case camelCase --public-type-case UpperCamelCase --private-type-case camelCase --no-prefix-fiat --doc-newline-in-typedef-bounds --doc-prepend-header 'Code generated by Fiat Cryptography. DO NOT EDIT.' --doc-text-before-function-name '' --doc-text-before-type-name '' --package-name secp256k1dettman '' 64 5 48 2 '2^256 - 4294968273' mul square
//
// curve description (via package name): secp256k1dettman
//
// machine_wordsize = 64 (from "64")
//
// requested operations: mul, square
//
// n = 5 (from "5")
//
// last_limb_width = 48 (from "48")
//
// last_reduction = 2 (from "2")
//
// s-c = 2^256 - [(1, 4294968273)] (from "2^256 - 4294968273")
//
// inbounds_multiplier: None (from "")
//
//
//
// Computed values:
//
//
//
//
package secp256k1dettman

import "math/bits"

type uint1 uint64 // We use uint64 instead of a more narrow type for performance reasons; see https://github.com/mit-plv/fiat-crypto/pull/1006#issuecomment-892625927
type int1 int64 // We use uint64 instead of a more narrow type for performance reasons; see https://github.com/mit-plv/fiat-crypto/pull/1006#issuecomment-892625927

// Mul multiplies two field elements.
//
// Postconditions:
//   eval out1 mod 115792089237316195423570985008687907853269984665640564039457584007908834671663 = (eval arg1 * eval arg2) mod 115792089237316195423570985008687907853269984665640564039457584007908834671663
//
// Input Bounds:
//   arg1: [[0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xffffffffffff0]]
//   arg2: [[0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xffffffffffff0]]
// Output Bounds:
//   out1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
func Mul(out1 *[5]uint64, arg1 *[5]uint64, arg2 *[5]uint64) {
	var x1 uint64
	var x2 uint64
	x2, x1 = bits.Mul64(arg1[4], arg2[4])
	var x3 uint64
	var x4 uint64
	x4, x3 = bits.Mul64(x1, 0x1000003d10)
	var x5 uint64
	var x6 uint64
	x6, x5 = bits.Mul64(arg1[3], arg2[0])
	var x7 uint64
	var x8 uint64
	x8, x7 = bits.Mul64(arg1[2], arg2[1])
	var x9 uint64
	var x10 uint64
	x9, x10 = bits.Add64(x7, x5, uint64(0x0))
	var x11 uint64
	x11, _ = bits.Add64(x8, x6, uint64(uint1(x10)))
	var x13 uint64
	var x14 uint64
	x14, x13 = bits.Mul64(arg1[1], arg2[2])
	var x15 uint64
	var x16 uint64
	x15, x16 = bits.Add64(x13, x9, uint64(0x0))
	var x17 uint64
	x17, _ = bits.Add64(x14, x11, uint64(uint1(x16)))
	var x19 uint64
	var x20 uint64
	x20, x19 = bits.Mul64(arg1[0], arg2[3])
	var x21 uint64
	var x22 uint64
	x21, x22 = bits.Add64(x19, x15, uint64(0x0))
	var x23 uint64
	x23, _ = bits.Add64(x20, x17, uint64(uint1(x22)))
	var x25 uint64
	var x26 uint64
	x25, x26 = bits.Add64(x21, x3, uint64(0x0))
	var x27 uint64
	x27, _ = bits.Add64(x23, x4, uint64(uint1(x26)))
	x29 := ((x25 >> 52) | ((x27 << 12) & 0xffffffffffffffff))
	x30 := (x25 & 0xfffffffffffff)
	var x31 uint64
	var x32 uint64
	x32, x31 = bits.Mul64(x2, 0x1000003d10000)
	var x33 uint64
	var x34 uint64
	x34, x33 = bits.Mul64(arg1[4], arg2[0])
	var x35 uint64
	var x36 uint64
	x36, x35 = bits.Mul64(arg1[3], arg2[1])
	var x37 uint64
	var x38 uint64
	x37, x38 = bits.Add64(x35, x33, uint64(0x0))
	var x39 uint64
	x39, _ = bits.Add64(x36, x34, uint64(uint1(x38)))
	var x41 uint64
	var x42 uint64
	x42, x41 = bits.Mul64(arg1[2], arg2[2])
	var x43 uint64
	var x44 uint64
	x43, x44 = bits.Add64(x41, x37, uint64(0x0))
	var x45 uint64
	x45, _ = bits.Add64(x42, x39, uint64(uint1(x44)))
	var x47 uint64
	var x48 uint64
	x48, x47 = bits.Mul64(arg1[1], arg2[3])
	var x49 uint64
	var x50 uint64
	x49, x50 = bits.Add64(x47, x43, uint64(0x0))
	var x51 uint64
	x51, _ = bits.Add64(x48, x45, uint64(uint1(x50)))
	var x53 uint64
	var x54 uint64
	x54, x53 = bits.Mul64(arg1[0], arg2[4])
	var x55 uint64
	var x56 uint64
	x55, x56 = bits.Add64(x53, x49, uint64(0x0))
	var x57 uint64
	x57, _ = bits.Add64(x54, x51, uint64(uint1(x56)))
	var x59 uint64
	var x60 uint64
	x59, x60 = bits.Add64(x29, x55, uint64(0x0))
	x61 := (uint64(uint1(x60)) + x57)
	var x62 uint64
	var x63 uint64
	x62, x63 = bits.Add64(x59, x31, uint64(0x0))
	var x64 uint64
	x64, _ = bits.Add64(x61, x32, uint64(uint1(x63)))
	x66 := ((x62 >> 52) | ((x64 << 12) & 0xffffffffffffffff))
	x67 := (x62 & 0xfffffffffffff)
	var x68 uint64
	var x69 uint64
	x69, x68 = bits.Mul64(arg1[4], arg2[1])
	var x70 uint64
	var x71 uint64
	x71, x70 = bits.Mul64(arg1[3], arg2[2])
	var x72 uint64
	var x73 uint64
	x72, x73 = bits.Add64(x70, x68, uint64(0x0))
	var x74 uint64
	x74, _ = bits.Add64(x71, x69, uint64(uint1(x73)))
	var x76 uint64
	var x77 uint64
	x77, x76 = bits.Mul64(arg1[2], arg2[3])
	var x78 uint64
	var x79 uint64
	x78, x79 = bits.Add64(x76, x72, uint64(0x0))
	var x80 uint64
	x80, _ = bits.Add64(x77, x74, uint64(uint1(x79)))
	var x82 uint64
	var x83 uint64
	x83, x82 = bits.Mul64(arg1[1], arg2[4])
	var x84 uint64
	var x85 uint64
	x84, x85 = bits.Add64(x82, x78, uint64(0x0))
	var x86 uint64
	x86, _ = bits.Add64(x83, x80, uint64(uint1(x85)))
	var x88 uint64
	var x89 uint64
	x88, x89 = bits.Add64(x66, x84, uint64(0x0))
	x90 := (uint64(uint1(x89)) + x86)
	x91 := ((x88 >> 52) | ((x90 << 12) & 0xffffffffffffffff))
	x92 := (x88 & 0xfffffffffffff)
	x93 := (x67 >> 48)
	x94 := (x67 & 0xffffffffffff)
	var x95 uint64
	var x96 uint64
	x96, x95 = bits.Mul64((x93 + (x92 << 4)), 0x1000003d1)
	var x97 uint64
	var x98 uint64
	x98, x97 = bits.Mul64(arg1[0], arg2[0])
	var x99 uint64
	var x100 uint64
	x99, x100 = bits.Add64(x97, x95, uint64(0x0))
	var x101 uint64
	x101, _ = bits.Add64(x98, x96, uint64(uint1(x100)))
	x103 := ((x99 >> 52) | ((x101 << 12) & 0xffffffffffffffff))
	x104 := (x99 & 0xfffffffffffff)
	var x105 uint64
	var x106 uint64
	x106, x105 = bits.Mul64(arg1[4], arg2[2])
	var x107 uint64
	var x108 uint64
	x108, x107 = bits.Mul64(arg1[3], arg2[3])
	var x109 uint64
	var x110 uint64
	x109, x110 = bits.Add64(x107, x105, uint64(0x0))
	var x111 uint64
	x111, _ = bits.Add64(x108, x106, uint64(uint1(x110)))
	var x113 uint64
	var x114 uint64
	x114, x113 = bits.Mul64(arg1[2], arg2[4])
	var x115 uint64
	var x116 uint64
	x115, x116 = bits.Add64(x113, x109, uint64(0x0))
	var x117 uint64
	x117, _ = bits.Add64(x114, x111, uint64(uint1(x116)))
	var x119 uint64
	var x120 uint64
	x119, x120 = bits.Add64(x91, x115, uint64(0x0))
	x121 := (uint64(uint1(x120)) + x117)
	x122 := ((x119 >> 52) | ((x121 << 12) & 0xffffffffffffffff))
	x123 := (x119 & 0xfffffffffffff)
	var x124 uint64
	var x125 uint64
	x125, x124 = bits.Mul64(x123, 0x1000003d10)
	var x126 uint64
	var x127 uint64
	x127, x126 = bits.Mul64(arg1[1], arg2[0])
	var x128 uint64
	var x129 uint64
	x129, x128 = bits.Mul64(arg1[0], arg2[1])
	var x130 uint64
	var x131 uint64
	x130, x131 = bits.Add64(x128, x126, uint64(0x0))
	var x132 uint64
	x132, _ = bits.Add64(x129, x127, uint64(uint1(x131)))
	var x134 uint64
	var x135 uint64
	x134, x135 = bits.Add64(x103, x130, uint64(0x0))
	x136 := (uint64(uint1(x135)) + x132)
	var x137 uint64
	var x138 uint64
	x137, x138 = bits.Add64(x134, x124, uint64(0x0))
	var x139 uint64
	x139, _ = bits.Add64(x136, x125, uint64(uint1(x138)))
	x141 := ((x137 >> 52) | ((x139 << 12) & 0xffffffffffffffff))
	x142 := (x137 & 0xfffffffffffff)
	var x143 uint64
	var x144 uint64
	x144, x143 = bits.Mul64(arg1[4], arg2[3])
	var x145 uint64
	var x146 uint64
	x146, x145 = bits.Mul64(arg1[3], arg2[4])
	var x147 uint64
	var x148 uint64
	x147, x148 = bits.Add64(x145, x143, uint64(0x0))
	var x149 uint64
	x149, _ = bits.Add64(x146, x144, uint64(uint1(x148)))
	var x151 uint64
	var x152 uint64
	x151, x152 = bits.Add64(x122, x147, uint64(0x0))
	x153 := (uint64(uint1(x152)) + x149)
	var x154 uint64
	var x155 uint64
	x155, x154 = bits.Mul64(x151, 0x1000003d10)
	var x156 uint64
	var x157 uint64
	x157, x156 = bits.Mul64(arg1[2], arg2[0])
	var x158 uint64
	var x159 uint64
	x159, x158 = bits.Mul64(arg1[1], arg2[1])
	var x160 uint64
	var x161 uint64
	x160, x161 = bits.Add64(x158, x156, uint64(0x0))
	var x162 uint64
	x162, _ = bits.Add64(x159, x157, uint64(uint1(x161)))
	var x164 uint64
	var x165 uint64
	x165, x164 = bits.Mul64(arg1[0], arg2[2])
	var x166 uint64
	var x167 uint64
	x166, x167 = bits.Add64(x164, x160, uint64(0x0))
	var x168 uint64
	x168, _ = bits.Add64(x165, x162, uint64(uint1(x167)))
	var x170 uint64
	var x171 uint64
	x170, x171 = bits.Add64(x141, x166, uint64(0x0))
	x172 := (uint64(uint1(x171)) + x168)
	var x173 uint64
	var x174 uint64
	x173, x174 = bits.Add64(x170, x154, uint64(0x0))
	var x175 uint64
	x175, _ = bits.Add64(x172, x155, uint64(uint1(x174)))
	x177 := ((x173 >> 52) | ((x175 << 12) & 0xffffffffffffffff))
	x178 := (x173 & 0xfffffffffffff)
	var x179 uint64
	var x180 uint64
	x180, x179 = bits.Mul64(x153, 0x1000003d10000)
	var x181 uint64
	var x182 uint64
	x181, x182 = bits.Add64((x177 + x30), x179, uint64(0x0))
	x183 := (uint64(uint1(x182)) + x180)
	x184 := ((x181 >> 52) | ((x183 << 12) & 0xffffffffffffffff))
	x185 := (x181 & 0xfffffffffffff)
	x186 := (x184 + x94)
	out1[0] = x104
	out1[1] = x142
	out1[2] = x178
	out1[3] = x185
	out1[4] = x186
}

// Square squares a field element.
//
// Postconditions:
//   eval out1 mod 115792089237316195423570985008687907853269984665640564039457584007908834671663 = (eval arg1 * eval arg1) mod 115792089237316195423570985008687907853269984665640564039457584007908834671663
//
// Input Bounds:
//   arg1: [[0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xfffffffffffff0], [0x0 ~> 0xffffffffffff0]]
// Output Bounds:
//   out1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
func Square(out1 *[5]uint64, arg1 *[5]uint64) {
	x1 := (arg1[3] * 0x2)
	x2 := (arg1[2] * 0x2)
	x3 := (arg1[1] * 0x2)
	x4 := (arg1[0] * 0x2)
	var x5 uint64
	var x6 uint64
	x6, x5 = bits.Mul64(arg1[4], arg1[4])
	var x7 uint64
	var x8 uint64
	x8, x7 = bits.Mul64(x5, 0x1000003d10)
	var x9 uint64
	var x10 uint64
	x10, x9 = bits.Mul64(x3, arg1[2])
	var x11 uint64
	var x12 uint64
	x12, x11 = bits.Mul64(x4, arg1[3])
	var x13 uint64
	var x14 uint64
	x13, x14 = bits.Add64(x11, x9, uint64(0x0))
	var x15 uint64
	x15, _ = bits.Add64(x12, x10, uint64(uint1(x14)))
	var x17 uint64
	var x18 uint64
	x17, x18 = bits.Add64(x13, x7, uint64(0x0))
	var x19 uint64
	x19, _ = bits.Add64(x15, x8, uint64(uint1(x18)))
	x21 := ((x17 >> 52) | ((x19 << 12) & 0xffffffffffffffff))
	x22 := (x17 & 0xfffffffffffff)
	var x23 uint64
	var x24 uint64
	x24, x23 = bits.Mul64(x6, 0x1000003d10000)
	var x25 uint64
	var x26 uint64
	x26, x25 = bits.Mul64(arg1[2], arg1[2])
	var x27 uint64
	var x28 uint64
	x28, x27 = bits.Mul64(x3, arg1[3])
	var x29 uint64
	var x30 uint64
	x29, x30 = bits.Add64(x27, x25, uint64(0x0))
	var x31 uint64
	x31, _ = bits.Add64(x28, x26, uint64(uint1(x30)))
	var x33 uint64
	var x34 uint64
	x34, x33 = bits.Mul64(x4, arg1[4])
	var x35 uint64
	var x36 uint64
	x35, x36 = bits.Add64(x33, x29, uint64(0x0))
	var x37 uint64
	x37, _ = bits.Add64(x34, x31, uint64(uint1(x36)))
	var x39 uint64
	var x40 uint64
	x39, x40 = bits.Add64(x21, x35, uint64(0x0))
	x41 := (uint64(uint1(x40)) + x37)
	var x42 uint64
	var x43 uint64
	x42, x43 = bits.Add64(x39, x23, uint64(0x0))
	var x44 uint64
	x44, _ = bits.Add64(x41, x24, uint64(uint1(x43)))
	x46 := ((x42 >> 52) | ((x44 << 12) & 0xffffffffffffffff))
	x47 := (x42 & 0xfffffffffffff)
	var x48 uint64
	var x49 uint64
	x49, x48 = bits.Mul64(x2, arg1[3])
	var x50 uint64
	var x51 uint64
	x51, x50 = bits.Mul64(x3, arg1[4])
	var x52 uint64
	var x53 uint64
	x52, x53 = bits.Add64(x50, x48, uint64(0x0))
	var x54 uint64
	x54, _ = bits.Add64(x51, x49, uint64(uint1(x53)))
	var x56 uint64
	var x57 uint64
	x56, x57 = bits.Add64(x46, x52, uint64(0x0))
	x58 := (uint64(uint1(x57)) + x54)
	x59 := ((x56 >> 52) | ((x58 << 12) & 0xffffffffffffffff))
	x60 := (x56 & 0xfffffffffffff)
	x61 := (x47 >> 48)
	x62 := (x47 & 0xffffffffffff)
	var x63 uint64
	var x64 uint64
	x64, x63 = bits.Mul64((x61 + (x60 << 4)), 0x1000003d1)
	var x65 uint64
	var x66 uint64
	x66, x65 = bits.Mul64(arg1[0], arg1[0])
	var x67 uint64
	var x68 uint64
	x67, x68 = bits.Add64(x65, x63, uint64(0x0))
	var x69 uint64
	x69, _ = bits.Add64(x66, x64, uint64(uint1(x68)))
	x71 := ((x67 >> 52) | ((x69 << 12) & 0xffffffffffffffff))
	x72 := (x67 & 0xfffffffffffff)
	var x73 uint64
	var x74 uint64
	x74, x73 = bits.Mul64(arg1[3], arg1[3])
	var x75 uint64
	var x76 uint64
	x76, x75 = bits.Mul64(x2, arg1[4])
	var x77 uint64
	var x78 uint64
	x77, x78 = bits.Add64(x75, x73, uint64(0x0))
	var x79 uint64
	x79, _ = bits.Add64(x76, x74, uint64(uint1(x78)))
	var x81 uint64
	var x82 uint64
	x81, x82 = bits.Add64(x59, x77, uint64(0x0))
	x83 := (uint64(uint1(x82)) + x79)
	x84 := ((x81 >> 52) | ((x83 << 12) & 0xffffffffffffffff))
	x85 := (x81 & 0xfffffffffffff)
	var x86 uint64
	var x87 uint64
	x87, x86 = bits.Mul64(x85, 0x1000003d10)
	var x88 uint64
	var x89 uint64
	x89, x88 = bits.Mul64(x4, arg1[1])
	var x90 uint64
	var x91 uint64
	x90, x91 = bits.Add64(x71, x88, uint64(0x0))
	x92 := (uint64(uint1(x91)) + x89)
	var x93 uint64
	var x94 uint64
	x93, x94 = bits.Add64(x90, x86, uint64(0x0))
	var x95 uint64
	x95, _ = bits.Add64(x92, x87, uint64(uint1(x94)))
	x97 := ((x93 >> 52) | ((x95 << 12) & 0xffffffffffffffff))
	x98 := (x93 & 0xfffffffffffff)
	var x99 uint64
	var x100 uint64
	x100, x99 = bits.Mul64(x1, arg1[4])
	var x101 uint64
	var x102 uint64
	x101, x102 = bits.Add64(x84, x99, uint64(0x0))
	x103 := (uint64(uint1(x102)) + x100)
	var x104 uint64
	var x105 uint64
	x105, x104 = bits.Mul64(x101, 0x1000003d10)
	var x106 uint64
	var x107 uint64
	x107, x106 = bits.Mul64(arg1[1], arg1[1])
	var x108 uint64
	var x109 uint64
	x109, x108 = bits.Mul64(x4, arg1[2])
	var x110 uint64
	var x111 uint64
	x110, x111 = bits.Add64(x108, x106, uint64(0x0))
	var x112 uint64
	x112, _ = bits.Add64(x109, x107, uint64(uint1(x111)))
	var x114 uint64
	var x115 uint64
	x114, x115 = bits.Add64(x97, x110, uint64(0x0))
	x116 := (uint64(uint1(x115)) + x112)
	var x117 uint64
	var x118 uint64
	x117, x118 = bits.Add64(x114, x104, uint64(0x0))
	var x119 uint64
	x119, _ = bits.Add64(x116, x105, uint64(uint1(x118)))
	x121 := ((x117 >> 52) | ((x119 << 12) & 0xffffffffffffffff))
	x122 := (x117 & 0xfffffffffffff)
	var x123 uint64
	var x124 uint64
	x124, x123 = bits.Mul64(x103, 0x1000003d10000)
	var x125 uint64
	var x126 uint64
	x125, x126 = bits.Add64((x121 + x22), x123, uint64(0x0))
	x127 := (uint64(uint1(x126)) + x124)
	x128 := ((x125 >> 52) | ((x127 << 12) & 0xffffffffffffffff))
	x129 := (x125 & 0xfffffffffffff)
	x130 := (x128 + x62)
	out1[0] = x72
	out1[1] = x98
	out1[2] = x122
	out1[3] = x129
	out1[4] = x130
}
