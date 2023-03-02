// Code generated by Fiat Cryptography. DO NOT EDIT.
//
// Autogenerated: 'src/ExtractionOCaml/dettman_multiplication' --lang Go --no-wide-int --relax-primitive-carry-to-bitwidth 32,64 --cmovznz-by-mul --internal-static --package-case flatcase --public-function-case UpperCamelCase --private-function-case camelCase --public-type-case UpperCamelCase --private-type-case camelCase --no-prefix-fiat --doc-newline-in-typedef-bounds --doc-prepend-header 'Code generated by Fiat Cryptography. DO NOT EDIT.' --doc-text-before-function-name '' --doc-text-before-type-name '' --package-name secp256k1dettman '' 64 5 52 '2^256 - 4294968273' mul
//
// curve description (via package name): secp256k1dettman
//
// machine_wordsize = 64 (from "64")
//
// requested operations: mul
//
// n = 5 (from "5")
//
// limbwidth = 52 (from "52")
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
//   arg1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
//   arg2: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1fffffffffffe]]
// Output Bounds:
//   out1: [[0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x1ffffffffffffe], [0x0 ~> 0x17fffffffffff]]
func Mul(out1 *[5]uint64, arg1 *[5]uint64, arg2 *[5]uint64) {
	var x1 uint64
	var x2 uint64
	x2, x1 = bits.Mul64(arg1[4], arg2[4])
	x3 := ((x1 >> 52) | ((x2 << 12) & 0xffffffffffffffff))
	x4 := (x1 & 0xfffffffffffff)
	var x5 uint64
	var x6 uint64
	x6, x5 = bits.Mul64(x4, 0x1000003d10)
	var x7 uint64
	var x8 uint64
	x8, x7 = bits.Mul64(arg1[3], arg2[0])
	var x9 uint64
	var x10 uint64
	x10, x9 = bits.Mul64(arg1[2], arg2[1])
	var x11 uint64
	var x12 uint64
	x11, x12 = bits.Add64(x9, x7, uint64(0x0))
	var x13 uint64
	x13, _ = bits.Add64(x10, x8, uint64(uint1(x12)))
	var x15 uint64
	var x16 uint64
	x16, x15 = bits.Mul64(arg1[1], arg2[2])
	var x17 uint64
	var x18 uint64
	x17, x18 = bits.Add64(x15, x11, uint64(0x0))
	var x19 uint64
	x19, _ = bits.Add64(x16, x13, uint64(uint1(x18)))
	var x21 uint64
	var x22 uint64
	x22, x21 = bits.Mul64(arg1[0], arg2[3])
	var x23 uint64
	var x24 uint64
	x23, x24 = bits.Add64(x21, x17, uint64(0x0))
	var x25 uint64
	x25, _ = bits.Add64(x22, x19, uint64(uint1(x24)))
	var x27 uint64
	var x28 uint64
	x27, x28 = bits.Add64(x23, x5, uint64(0x0))
	var x29 uint64
	x29, _ = bits.Add64(x25, x6, uint64(uint1(x28)))
	x31 := ((x27 >> 52) | ((x29 << 12) & 0xffffffffffffffff))
	x32 := (x27 & 0xfffffffffffff)
	var x33 uint64
	var x34 uint64
	x34, x33 = bits.Mul64(x3, 0x1000003d10)
	var x35 uint64
	var x36 uint64
	x36, x35 = bits.Mul64(arg1[4], arg2[0])
	var x37 uint64
	var x38 uint64
	x38, x37 = bits.Mul64(arg1[3], arg2[1])
	var x39 uint64
	var x40 uint64
	x39, x40 = bits.Add64(x37, x35, uint64(0x0))
	var x41 uint64
	x41, _ = bits.Add64(x38, x36, uint64(uint1(x40)))
	var x43 uint64
	var x44 uint64
	x44, x43 = bits.Mul64(arg1[2], arg2[2])
	var x45 uint64
	var x46 uint64
	x45, x46 = bits.Add64(x43, x39, uint64(0x0))
	var x47 uint64
	x47, _ = bits.Add64(x44, x41, uint64(uint1(x46)))
	var x49 uint64
	var x50 uint64
	x50, x49 = bits.Mul64(arg1[1], arg2[3])
	var x51 uint64
	var x52 uint64
	x51, x52 = bits.Add64(x49, x45, uint64(0x0))
	var x53 uint64
	x53, _ = bits.Add64(x50, x47, uint64(uint1(x52)))
	var x55 uint64
	var x56 uint64
	x56, x55 = bits.Mul64(arg1[0], arg2[4])
	var x57 uint64
	var x58 uint64
	x57, x58 = bits.Add64(x55, x51, uint64(0x0))
	var x59 uint64
	x59, _ = bits.Add64(x56, x53, uint64(uint1(x58)))
	var x61 uint64
	var x62 uint64
	x61, x62 = bits.Add64(x57, x31, uint64(0x0))
	x63 := (uint64(uint1(x62)) + x59)
	var x64 uint64
	var x65 uint64
	x64, x65 = bits.Add64(x61, x33, uint64(0x0))
	var x66 uint64
	x66, _ = bits.Add64(x63, x34, uint64(uint1(x65)))
	x68 := ((x64 >> 52) | ((x66 << 12) & 0xffffffffffffffff))
	x69 := (x64 & 0xfffffffffffff)
	x70 := (x69 >> 48)
	x71 := (x69 & 0xffffffffffff)
	var x72 uint64
	var x73 uint64
	x73, x72 = bits.Mul64(arg1[4], arg2[1])
	var x74 uint64
	var x75 uint64
	x75, x74 = bits.Mul64(arg1[3], arg2[2])
	var x76 uint64
	var x77 uint64
	x76, x77 = bits.Add64(x74, x72, uint64(0x0))
	var x78 uint64
	x78, _ = bits.Add64(x75, x73, uint64(uint1(x77)))
	var x80 uint64
	var x81 uint64
	x81, x80 = bits.Mul64(arg1[2], arg2[3])
	var x82 uint64
	var x83 uint64
	x82, x83 = bits.Add64(x80, x76, uint64(0x0))
	var x84 uint64
	x84, _ = bits.Add64(x81, x78, uint64(uint1(x83)))
	var x86 uint64
	var x87 uint64
	x87, x86 = bits.Mul64(arg1[1], arg2[4])
	var x88 uint64
	var x89 uint64
	x88, x89 = bits.Add64(x86, x82, uint64(0x0))
	var x90 uint64
	x90, _ = bits.Add64(x87, x84, uint64(uint1(x89)))
	var x92 uint64
	var x93 uint64
	x92, x93 = bits.Add64(x88, x68, uint64(0x0))
	x94 := (uint64(uint1(x93)) + x90)
	x95 := ((x92 >> 52) | ((x94 << 12) & 0xffffffffffffffff))
	x96 := (x92 & 0xfffffffffffff)
	var x97 uint64
	var x98 uint64
	x98, x97 = bits.Mul64(((x96 << 4) + x70), 0x1000003d1)
	var x99 uint64
	var x100 uint64
	x100, x99 = bits.Mul64(arg1[0], arg2[0])
	var x101 uint64
	var x102 uint64
	x101, x102 = bits.Add64(x99, x97, uint64(0x0))
	var x103 uint64
	x103, _ = bits.Add64(x100, x98, uint64(uint1(x102)))
	x105 := ((x101 >> 52) | ((x103 << 12) & 0xffffffffffffffff))
	x106 := (x101 & 0xfffffffffffff)
	var x107 uint64
	var x108 uint64
	x108, x107 = bits.Mul64(arg1[4], arg2[2])
	var x109 uint64
	var x110 uint64
	x110, x109 = bits.Mul64(arg1[3], arg2[3])
	var x111 uint64
	var x112 uint64
	x111, x112 = bits.Add64(x109, x107, uint64(0x0))
	var x113 uint64
	x113, _ = bits.Add64(x110, x108, uint64(uint1(x112)))
	var x115 uint64
	var x116 uint64
	x116, x115 = bits.Mul64(arg1[2], arg2[4])
	var x117 uint64
	var x118 uint64
	x117, x118 = bits.Add64(x115, x111, uint64(0x0))
	var x119 uint64
	x119, _ = bits.Add64(x116, x113, uint64(uint1(x118)))
	var x121 uint64
	var x122 uint64
	x121, x122 = bits.Add64(x117, x95, uint64(0x0))
	x123 := (uint64(uint1(x122)) + x119)
	x124 := ((x121 >> 52) | ((x123 << 12) & 0xffffffffffffffff))
	x125 := (x121 & 0xfffffffffffff)
	var x126 uint64
	var x127 uint64
	x127, x126 = bits.Mul64(x125, 0x1000003d10)
	var x128 uint64
	var x129 uint64
	x129, x128 = bits.Mul64(arg1[1], arg2[0])
	var x130 uint64
	var x131 uint64
	x131, x130 = bits.Mul64(arg1[0], arg2[1])
	var x132 uint64
	var x133 uint64
	x132, x133 = bits.Add64(x130, x128, uint64(0x0))
	var x134 uint64
	x134, _ = bits.Add64(x131, x129, uint64(uint1(x133)))
	var x136 uint64
	var x137 uint64
	x136, x137 = bits.Add64(x132, x105, uint64(0x0))
	x138 := (uint64(uint1(x137)) + x134)
	var x139 uint64
	var x140 uint64
	x139, x140 = bits.Add64(x136, x126, uint64(0x0))
	var x141 uint64
	x141, _ = bits.Add64(x138, x127, uint64(uint1(x140)))
	x143 := ((x139 >> 52) | ((x141 << 12) & 0xffffffffffffffff))
	x144 := (x139 & 0xfffffffffffff)
	var x145 uint64
	var x146 uint64
	x146, x145 = bits.Mul64(arg1[4], arg2[3])
	var x147 uint64
	var x148 uint64
	x148, x147 = bits.Mul64(arg1[3], arg2[4])
	var x149 uint64
	var x150 uint64
	x149, x150 = bits.Add64(x147, x145, uint64(0x0))
	var x151 uint64
	x151, _ = bits.Add64(x148, x146, uint64(uint1(x150)))
	var x153 uint64
	var x154 uint64
	x153, x154 = bits.Add64(x149, x124, uint64(0x0))
	x155 := (uint64(uint1(x154)) + x151)
	x156 := ((x153 >> 52) | ((x155 << 12) & 0xffffffffffffffff))
	x157 := (x153 & 0xfffffffffffff)
	var x158 uint64
	var x159 uint64
	x159, x158 = bits.Mul64(x157, 0x1000003d10)
	var x160 uint64
	var x161 uint64
	x161, x160 = bits.Mul64(arg1[2], arg2[0])
	var x162 uint64
	var x163 uint64
	x163, x162 = bits.Mul64(arg1[1], arg2[1])
	var x164 uint64
	var x165 uint64
	x164, x165 = bits.Add64(x162, x160, uint64(0x0))
	var x166 uint64
	x166, _ = bits.Add64(x163, x161, uint64(uint1(x165)))
	var x168 uint64
	var x169 uint64
	x169, x168 = bits.Mul64(arg1[0], arg2[2])
	var x170 uint64
	var x171 uint64
	x170, x171 = bits.Add64(x168, x164, uint64(0x0))
	var x172 uint64
	x172, _ = bits.Add64(x169, x166, uint64(uint1(x171)))
	var x174 uint64
	var x175 uint64
	x174, x175 = bits.Add64(x170, x143, uint64(0x0))
	x176 := (uint64(uint1(x175)) + x172)
	var x177 uint64
	var x178 uint64
	x177, x178 = bits.Add64(x174, x158, uint64(0x0))
	var x179 uint64
	x179, _ = bits.Add64(x176, x159, uint64(uint1(x178)))
	x181 := ((x177 >> 52) | ((x179 << 12) & 0xffffffffffffffff))
	x182 := (x177 & 0xfffffffffffff)
	var x183 uint64
	var x184 uint64
	x184, x183 = bits.Mul64(x156, 0x1000003d10)
	var x185 uint64
	var x186 uint64
	x185, x186 = bits.Add64((x32 + x181), x183, uint64(0x0))
	x187 := (uint64(uint1(x186)) + x184)
	x188 := ((x185 >> 52) | ((x187 << 12) & 0xffffffffffffffff))
	x189 := (x185 & 0xfffffffffffff)
	x190 := (x71 + x188)
	out1[0] = x106
	out1[1] = x144
	out1[2] = x182
	out1[3] = x189
	out1[4] = x190
}
