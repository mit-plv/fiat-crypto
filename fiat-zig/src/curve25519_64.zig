// Autogenerated: 'src/ExtractionOCaml/unsaturated_solinas' --lang Zig --internal-static --public-function-case camelCase --private-function-case camelCase --public-type-case UpperCamelCase --private-type-case UpperCamelCase --no-prefix-fiat --package-name 25519 '' 64 '(auto)' '2^255 - 19' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes relax carry_scmul121666
// curve description (via package name): 25519
// machine_wordsize = 64 (from "64")
// requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes, relax, carry_scmul121666
// n = 5 (from "(auto)")
// s-c = 2^255 - [(1, 19)] (from "2^255 - 19")
// tight_bounds_multiplier = 1 (from "")
//
// Computed values:
//   carry_chain = [0, 1, 2, 3, 4, 0, 1]
//   eval z = z[0] + (z[1] << 51) + (z[2] << 102) + (z[3] << 153) + (z[4] << 204)
//   bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128) + (z[17] << 136) + (z[18] << 144) + (z[19] << 152) + (z[20] << 160) + (z[21] << 168) + (z[22] << 176) + (z[23] << 184) + (z[24] << 192) + (z[25] << 200) + (z[26] << 208) + (z[27] << 216) + (z[28] << 224) + (z[29] << 232) + (z[30] << 240) + (z[31] << 248)
//   balance = [0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]

const std = @import("std");
const cast = std.meta.cast;
const mode = std.builtin.mode; // Checked arithmetic is disabled in non-debug modes to avoid side channels

// The type LooseFieldElement is a field element with loose bounds.
// Bounds: [[0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000], [0x0 ~> 0x18000000000000]]
pub const LooseFieldElement = [5]u64;

// The type TightFieldElement is a field element with tight bounds.
// Bounds: [[0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000], [0x0 ~> 0x8000000000000]]
pub const TightFieldElement = [5]u64;

/// The function addcarryxU51 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^51
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^51⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffffff]
///   out2: [0x0 ~> 0x1]
inline fn addcarryxU51(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((cast(u64, arg1) + arg2) + arg3);
    const x2 = (x1 & 0x7ffffffffffff);
    const x3 = cast(u1, (x1 >> 51));
    out1.* = x2;
    out2.* = x3;
}

/// The function subborrowxU51 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^51
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^51⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffffff]
///   out2: [0x0 ~> 0x1]
inline fn subborrowxU51(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = cast(i64, (cast(i128, cast(i64, (cast(i128, arg2) - cast(i128, arg1)))) - cast(i128, arg3)));
    const x2 = cast(i1, (x1 >> 51));
    const x3 = cast(u64, (cast(i128, x1) & cast(i128, 0x7ffffffffffff)));
    out1.* = x3;
    out2.* = cast(u1, (cast(i2, 0x0) - cast(i2, x2)));
}

/// The function cmovznzU64 is a single-word conditional move.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xffffffffffffffff]
///   arg3: [0x0 ~> 0xffffffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xffffffffffffffff]
inline fn cmovznzU64(out1: *u64, arg1: u1, arg2: u64, arg3: u64) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (~(~arg1));
    const x2 = cast(u64, (cast(i128, cast(i1, (cast(i2, 0x0) - cast(i2, x1)))) & cast(i128, 0xffffffffffffffff)));
    const x3 = ((x2 & arg3) | ((~x2) & arg2));
    out1.* = x3;
}

/// The function carryMul multiplies two field elements and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg2) mod m
///
pub fn carryMul(out1: *TightFieldElement, arg1: LooseFieldElement, arg2: LooseFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u128, (arg1[4])) * cast(u128, ((arg2[4]) * 0x13)));
    const x2 = (cast(u128, (arg1[4])) * cast(u128, ((arg2[3]) * 0x13)));
    const x3 = (cast(u128, (arg1[4])) * cast(u128, ((arg2[2]) * 0x13)));
    const x4 = (cast(u128, (arg1[4])) * cast(u128, ((arg2[1]) * 0x13)));
    const x5 = (cast(u128, (arg1[3])) * cast(u128, ((arg2[4]) * 0x13)));
    const x6 = (cast(u128, (arg1[3])) * cast(u128, ((arg2[3]) * 0x13)));
    const x7 = (cast(u128, (arg1[3])) * cast(u128, ((arg2[2]) * 0x13)));
    const x8 = (cast(u128, (arg1[2])) * cast(u128, ((arg2[4]) * 0x13)));
    const x9 = (cast(u128, (arg1[2])) * cast(u128, ((arg2[3]) * 0x13)));
    const x10 = (cast(u128, (arg1[1])) * cast(u128, ((arg2[4]) * 0x13)));
    const x11 = (cast(u128, (arg1[4])) * cast(u128, (arg2[0])));
    const x12 = (cast(u128, (arg1[3])) * cast(u128, (arg2[1])));
    const x13 = (cast(u128, (arg1[3])) * cast(u128, (arg2[0])));
    const x14 = (cast(u128, (arg1[2])) * cast(u128, (arg2[2])));
    const x15 = (cast(u128, (arg1[2])) * cast(u128, (arg2[1])));
    const x16 = (cast(u128, (arg1[2])) * cast(u128, (arg2[0])));
    const x17 = (cast(u128, (arg1[1])) * cast(u128, (arg2[3])));
    const x18 = (cast(u128, (arg1[1])) * cast(u128, (arg2[2])));
    const x19 = (cast(u128, (arg1[1])) * cast(u128, (arg2[1])));
    const x20 = (cast(u128, (arg1[1])) * cast(u128, (arg2[0])));
    const x21 = (cast(u128, (arg1[0])) * cast(u128, (arg2[4])));
    const x22 = (cast(u128, (arg1[0])) * cast(u128, (arg2[3])));
    const x23 = (cast(u128, (arg1[0])) * cast(u128, (arg2[2])));
    const x24 = (cast(u128, (arg1[0])) * cast(u128, (arg2[1])));
    const x25 = (cast(u128, (arg1[0])) * cast(u128, (arg2[0])));
    const x26 = (x25 + (x10 + (x9 + (x7 + x4))));
    const x27 = cast(u64, (x26 >> 51));
    const x28 = cast(u64, (x26 & cast(u128, 0x7ffffffffffff)));
    const x29 = (x21 + (x17 + (x14 + (x12 + x11))));
    const x30 = (x22 + (x18 + (x15 + (x13 + x1))));
    const x31 = (x23 + (x19 + (x16 + (x5 + x2))));
    const x32 = (x24 + (x20 + (x8 + (x6 + x3))));
    const x33 = (cast(u128, x27) + x32);
    const x34 = cast(u64, (x33 >> 51));
    const x35 = cast(u64, (x33 & cast(u128, 0x7ffffffffffff)));
    const x36 = (cast(u128, x34) + x31);
    const x37 = cast(u64, (x36 >> 51));
    const x38 = cast(u64, (x36 & cast(u128, 0x7ffffffffffff)));
    const x39 = (cast(u128, x37) + x30);
    const x40 = cast(u64, (x39 >> 51));
    const x41 = cast(u64, (x39 & cast(u128, 0x7ffffffffffff)));
    const x42 = (cast(u128, x40) + x29);
    const x43 = cast(u64, (x42 >> 51));
    const x44 = cast(u64, (x42 & cast(u128, 0x7ffffffffffff)));
    const x45 = (x43 * 0x13);
    const x46 = (x28 + x45);
    const x47 = (x46 >> 51);
    const x48 = (x46 & 0x7ffffffffffff);
    const x49 = (x47 + x35);
    const x50 = cast(u1, (x49 >> 51));
    const x51 = (x49 & 0x7ffffffffffff);
    const x52 = (cast(u64, x50) + x38);
    out1[0] = x48;
    out1[1] = x51;
    out1[2] = x52;
    out1[3] = x41;
    out1[4] = x44;
}

/// The function carrySquare squares a field element and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg1) mod m
///
pub fn carrySquare(out1: *TightFieldElement, arg1: LooseFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((arg1[4]) * 0x13);
    const x2 = (x1 * 0x2);
    const x3 = ((arg1[4]) * 0x2);
    const x4 = ((arg1[3]) * 0x13);
    const x5 = (x4 * 0x2);
    const x6 = ((arg1[3]) * 0x2);
    const x7 = ((arg1[2]) * 0x2);
    const x8 = ((arg1[1]) * 0x2);
    const x9 = (cast(u128, (arg1[4])) * cast(u128, x1));
    const x10 = (cast(u128, (arg1[3])) * cast(u128, x2));
    const x11 = (cast(u128, (arg1[3])) * cast(u128, x4));
    const x12 = (cast(u128, (arg1[2])) * cast(u128, x2));
    const x13 = (cast(u128, (arg1[2])) * cast(u128, x5));
    const x14 = (cast(u128, (arg1[2])) * cast(u128, (arg1[2])));
    const x15 = (cast(u128, (arg1[1])) * cast(u128, x2));
    const x16 = (cast(u128, (arg1[1])) * cast(u128, x6));
    const x17 = (cast(u128, (arg1[1])) * cast(u128, x7));
    const x18 = (cast(u128, (arg1[1])) * cast(u128, (arg1[1])));
    const x19 = (cast(u128, (arg1[0])) * cast(u128, x3));
    const x20 = (cast(u128, (arg1[0])) * cast(u128, x6));
    const x21 = (cast(u128, (arg1[0])) * cast(u128, x7));
    const x22 = (cast(u128, (arg1[0])) * cast(u128, x8));
    const x23 = (cast(u128, (arg1[0])) * cast(u128, (arg1[0])));
    const x24 = (x23 + (x15 + x13));
    const x25 = cast(u64, (x24 >> 51));
    const x26 = cast(u64, (x24 & cast(u128, 0x7ffffffffffff)));
    const x27 = (x19 + (x16 + x14));
    const x28 = (x20 + (x17 + x9));
    const x29 = (x21 + (x18 + x10));
    const x30 = (x22 + (x12 + x11));
    const x31 = (cast(u128, x25) + x30);
    const x32 = cast(u64, (x31 >> 51));
    const x33 = cast(u64, (x31 & cast(u128, 0x7ffffffffffff)));
    const x34 = (cast(u128, x32) + x29);
    const x35 = cast(u64, (x34 >> 51));
    const x36 = cast(u64, (x34 & cast(u128, 0x7ffffffffffff)));
    const x37 = (cast(u128, x35) + x28);
    const x38 = cast(u64, (x37 >> 51));
    const x39 = cast(u64, (x37 & cast(u128, 0x7ffffffffffff)));
    const x40 = (cast(u128, x38) + x27);
    const x41 = cast(u64, (x40 >> 51));
    const x42 = cast(u64, (x40 & cast(u128, 0x7ffffffffffff)));
    const x43 = (x41 * 0x13);
    const x44 = (x26 + x43);
    const x45 = (x44 >> 51);
    const x46 = (x44 & 0x7ffffffffffff);
    const x47 = (x45 + x33);
    const x48 = cast(u1, (x47 >> 51));
    const x49 = (x47 & 0x7ffffffffffff);
    const x50 = (cast(u64, x48) + x36);
    out1[0] = x46;
    out1[1] = x49;
    out1[2] = x50;
    out1[3] = x39;
    out1[4] = x42;
}

/// The function carry reduces a field element.
///
/// Postconditions:
///   eval out1 mod m = eval arg1 mod m
///
pub fn carry(out1: *TightFieldElement, arg1: LooseFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (arg1[0]);
    const x2 = ((x1 >> 51) + (arg1[1]));
    const x3 = ((x2 >> 51) + (arg1[2]));
    const x4 = ((x3 >> 51) + (arg1[3]));
    const x5 = ((x4 >> 51) + (arg1[4]));
    const x6 = ((x1 & 0x7ffffffffffff) + ((x5 >> 51) * 0x13));
    const x7 = (cast(u64, cast(u1, (x6 >> 51))) + (x2 & 0x7ffffffffffff));
    const x8 = (x6 & 0x7ffffffffffff);
    const x9 = (x7 & 0x7ffffffffffff);
    const x10 = (cast(u64, cast(u1, (x7 >> 51))) + (x3 & 0x7ffffffffffff));
    const x11 = (x4 & 0x7ffffffffffff);
    const x12 = (x5 & 0x7ffffffffffff);
    out1[0] = x8;
    out1[1] = x9;
    out1[2] = x10;
    out1[3] = x11;
    out1[4] = x12;
}

/// The function add adds two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 + eval arg2) mod m
///
pub fn add(out1: *LooseFieldElement, arg1: TightFieldElement, arg2: TightFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((arg1[0]) + (arg2[0]));
    const x2 = ((arg1[1]) + (arg2[1]));
    const x3 = ((arg1[2]) + (arg2[2]));
    const x4 = ((arg1[3]) + (arg2[3]));
    const x5 = ((arg1[4]) + (arg2[4]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function sub subtracts two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 - eval arg2) mod m
///
pub fn sub(out1: *LooseFieldElement, arg1: TightFieldElement, arg2: TightFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((0xfffffffffffda + (arg1[0])) - (arg2[0]));
    const x2 = ((0xffffffffffffe + (arg1[1])) - (arg2[1]));
    const x3 = ((0xffffffffffffe + (arg1[2])) - (arg2[2]));
    const x4 = ((0xffffffffffffe + (arg1[3])) - (arg2[3]));
    const x5 = ((0xffffffffffffe + (arg1[4])) - (arg2[4]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function opp negates a field element.
///
/// Postconditions:
///   eval out1 mod m = -eval arg1 mod m
///
pub fn opp(out1: *LooseFieldElement, arg1: TightFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (0xfffffffffffda - (arg1[0]));
    const x2 = (0xffffffffffffe - (arg1[1]));
    const x3 = (0xffffffffffffe - (arg1[2]));
    const x4 = (0xffffffffffffe - (arg1[3]));
    const x5 = (0xffffffffffffe - (arg1[4]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function selectznz is a multi-limb conditional select.
///
/// Postconditions:
///   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
///   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
pub fn selectznz(out1: *[5]u64, arg1: u1, arg2: [5]u64, arg3: [5]u64) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u64 = undefined;
    cmovznzU64(&x1, arg1, (arg2[0]), (arg3[0]));
    var x2: u64 = undefined;
    cmovznzU64(&x2, arg1, (arg2[1]), (arg3[1]));
    var x3: u64 = undefined;
    cmovznzU64(&x3, arg1, (arg2[2]), (arg3[2]));
    var x4: u64 = undefined;
    cmovznzU64(&x4, arg1, (arg2[3]), (arg3[3]));
    var x5: u64 = undefined;
    cmovznzU64(&x5, arg1, (arg2[4]), (arg3[4]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function toBytes serializes a field element to bytes in little-endian order.
///
/// Postconditions:
///   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..31]
///
/// Output Bounds:
///   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
pub fn toBytes(out1: *[32]u8, arg1: TightFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u64 = undefined;
    var x2: u1 = undefined;
    subborrowxU51(&x1, &x2, 0x0, (arg1[0]), 0x7ffffffffffed);
    var x3: u64 = undefined;
    var x4: u1 = undefined;
    subborrowxU51(&x3, &x4, x2, (arg1[1]), 0x7ffffffffffff);
    var x5: u64 = undefined;
    var x6: u1 = undefined;
    subborrowxU51(&x5, &x6, x4, (arg1[2]), 0x7ffffffffffff);
    var x7: u64 = undefined;
    var x8: u1 = undefined;
    subborrowxU51(&x7, &x8, x6, (arg1[3]), 0x7ffffffffffff);
    var x9: u64 = undefined;
    var x10: u1 = undefined;
    subborrowxU51(&x9, &x10, x8, (arg1[4]), 0x7ffffffffffff);
    var x11: u64 = undefined;
    cmovznzU64(&x11, x10, cast(u64, 0x0), 0xffffffffffffffff);
    var x12: u64 = undefined;
    var x13: u1 = undefined;
    addcarryxU51(&x12, &x13, 0x0, x1, (x11 & 0x7ffffffffffed));
    var x14: u64 = undefined;
    var x15: u1 = undefined;
    addcarryxU51(&x14, &x15, x13, x3, (x11 & 0x7ffffffffffff));
    var x16: u64 = undefined;
    var x17: u1 = undefined;
    addcarryxU51(&x16, &x17, x15, x5, (x11 & 0x7ffffffffffff));
    var x18: u64 = undefined;
    var x19: u1 = undefined;
    addcarryxU51(&x18, &x19, x17, x7, (x11 & 0x7ffffffffffff));
    var x20: u64 = undefined;
    var x21: u1 = undefined;
    addcarryxU51(&x20, &x21, x19, x9, (x11 & 0x7ffffffffffff));
    const x22 = (x20 << 4);
    const x23 = (x18 * cast(u64, 0x2));
    const x24 = (x16 << 6);
    const x25 = (x14 << 3);
    const x26 = cast(u8, (x12 & cast(u64, 0xff)));
    const x27 = (x12 >> 8);
    const x28 = cast(u8, (x27 & cast(u64, 0xff)));
    const x29 = (x27 >> 8);
    const x30 = cast(u8, (x29 & cast(u64, 0xff)));
    const x31 = (x29 >> 8);
    const x32 = cast(u8, (x31 & cast(u64, 0xff)));
    const x33 = (x31 >> 8);
    const x34 = cast(u8, (x33 & cast(u64, 0xff)));
    const x35 = (x33 >> 8);
    const x36 = cast(u8, (x35 & cast(u64, 0xff)));
    const x37 = cast(u8, (x35 >> 8));
    const x38 = (x25 + cast(u64, x37));
    const x39 = cast(u8, (x38 & cast(u64, 0xff)));
    const x40 = (x38 >> 8);
    const x41 = cast(u8, (x40 & cast(u64, 0xff)));
    const x42 = (x40 >> 8);
    const x43 = cast(u8, (x42 & cast(u64, 0xff)));
    const x44 = (x42 >> 8);
    const x45 = cast(u8, (x44 & cast(u64, 0xff)));
    const x46 = (x44 >> 8);
    const x47 = cast(u8, (x46 & cast(u64, 0xff)));
    const x48 = (x46 >> 8);
    const x49 = cast(u8, (x48 & cast(u64, 0xff)));
    const x50 = cast(u8, (x48 >> 8));
    const x51 = (x24 + cast(u64, x50));
    const x52 = cast(u8, (x51 & cast(u64, 0xff)));
    const x53 = (x51 >> 8);
    const x54 = cast(u8, (x53 & cast(u64, 0xff)));
    const x55 = (x53 >> 8);
    const x56 = cast(u8, (x55 & cast(u64, 0xff)));
    const x57 = (x55 >> 8);
    const x58 = cast(u8, (x57 & cast(u64, 0xff)));
    const x59 = (x57 >> 8);
    const x60 = cast(u8, (x59 & cast(u64, 0xff)));
    const x61 = (x59 >> 8);
    const x62 = cast(u8, (x61 & cast(u64, 0xff)));
    const x63 = (x61 >> 8);
    const x64 = cast(u8, (x63 & cast(u64, 0xff)));
    const x65 = cast(u1, (x63 >> 8));
    const x66 = (x23 + cast(u64, x65));
    const x67 = cast(u8, (x66 & cast(u64, 0xff)));
    const x68 = (x66 >> 8);
    const x69 = cast(u8, (x68 & cast(u64, 0xff)));
    const x70 = (x68 >> 8);
    const x71 = cast(u8, (x70 & cast(u64, 0xff)));
    const x72 = (x70 >> 8);
    const x73 = cast(u8, (x72 & cast(u64, 0xff)));
    const x74 = (x72 >> 8);
    const x75 = cast(u8, (x74 & cast(u64, 0xff)));
    const x76 = (x74 >> 8);
    const x77 = cast(u8, (x76 & cast(u64, 0xff)));
    const x78 = cast(u8, (x76 >> 8));
    const x79 = (x22 + cast(u64, x78));
    const x80 = cast(u8, (x79 & cast(u64, 0xff)));
    const x81 = (x79 >> 8);
    const x82 = cast(u8, (x81 & cast(u64, 0xff)));
    const x83 = (x81 >> 8);
    const x84 = cast(u8, (x83 & cast(u64, 0xff)));
    const x85 = (x83 >> 8);
    const x86 = cast(u8, (x85 & cast(u64, 0xff)));
    const x87 = (x85 >> 8);
    const x88 = cast(u8, (x87 & cast(u64, 0xff)));
    const x89 = (x87 >> 8);
    const x90 = cast(u8, (x89 & cast(u64, 0xff)));
    const x91 = cast(u8, (x89 >> 8));
    out1[0] = x26;
    out1[1] = x28;
    out1[2] = x30;
    out1[3] = x32;
    out1[4] = x34;
    out1[5] = x36;
    out1[6] = x39;
    out1[7] = x41;
    out1[8] = x43;
    out1[9] = x45;
    out1[10] = x47;
    out1[11] = x49;
    out1[12] = x52;
    out1[13] = x54;
    out1[14] = x56;
    out1[15] = x58;
    out1[16] = x60;
    out1[17] = x62;
    out1[18] = x64;
    out1[19] = x67;
    out1[20] = x69;
    out1[21] = x71;
    out1[22] = x73;
    out1[23] = x75;
    out1[24] = x77;
    out1[25] = x80;
    out1[26] = x82;
    out1[27] = x84;
    out1[28] = x86;
    out1[29] = x88;
    out1[30] = x90;
    out1[31] = x91;
}

/// The function fromBytes deserializes a field element from bytes in little-endian order.
///
/// Postconditions:
///   eval out1 mod m = bytes_eval arg1 mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
pub fn fromBytes(out1: *TightFieldElement, arg1: [32]u8) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u64, (arg1[31])) << 44);
    const x2 = (cast(u64, (arg1[30])) << 36);
    const x3 = (cast(u64, (arg1[29])) << 28);
    const x4 = (cast(u64, (arg1[28])) << 20);
    const x5 = (cast(u64, (arg1[27])) << 12);
    const x6 = (cast(u64, (arg1[26])) << 4);
    const x7 = (cast(u64, (arg1[25])) << 47);
    const x8 = (cast(u64, (arg1[24])) << 39);
    const x9 = (cast(u64, (arg1[23])) << 31);
    const x10 = (cast(u64, (arg1[22])) << 23);
    const x11 = (cast(u64, (arg1[21])) << 15);
    const x12 = (cast(u64, (arg1[20])) << 7);
    const x13 = (cast(u64, (arg1[19])) << 50);
    const x14 = (cast(u64, (arg1[18])) << 42);
    const x15 = (cast(u64, (arg1[17])) << 34);
    const x16 = (cast(u64, (arg1[16])) << 26);
    const x17 = (cast(u64, (arg1[15])) << 18);
    const x18 = (cast(u64, (arg1[14])) << 10);
    const x19 = (cast(u64, (arg1[13])) << 2);
    const x20 = (cast(u64, (arg1[12])) << 45);
    const x21 = (cast(u64, (arg1[11])) << 37);
    const x22 = (cast(u64, (arg1[10])) << 29);
    const x23 = (cast(u64, (arg1[9])) << 21);
    const x24 = (cast(u64, (arg1[8])) << 13);
    const x25 = (cast(u64, (arg1[7])) << 5);
    const x26 = (cast(u64, (arg1[6])) << 48);
    const x27 = (cast(u64, (arg1[5])) << 40);
    const x28 = (cast(u64, (arg1[4])) << 32);
    const x29 = (cast(u64, (arg1[3])) << 24);
    const x30 = (cast(u64, (arg1[2])) << 16);
    const x31 = (cast(u64, (arg1[1])) << 8);
    const x32 = (arg1[0]);
    const x33 = (x31 + cast(u64, x32));
    const x34 = (x30 + x33);
    const x35 = (x29 + x34);
    const x36 = (x28 + x35);
    const x37 = (x27 + x36);
    const x38 = (x26 + x37);
    const x39 = (x38 & 0x7ffffffffffff);
    const x40 = cast(u8, (x38 >> 51));
    const x41 = (x25 + cast(u64, x40));
    const x42 = (x24 + x41);
    const x43 = (x23 + x42);
    const x44 = (x22 + x43);
    const x45 = (x21 + x44);
    const x46 = (x20 + x45);
    const x47 = (x46 & 0x7ffffffffffff);
    const x48 = cast(u8, (x46 >> 51));
    const x49 = (x19 + cast(u64, x48));
    const x50 = (x18 + x49);
    const x51 = (x17 + x50);
    const x52 = (x16 + x51);
    const x53 = (x15 + x52);
    const x54 = (x14 + x53);
    const x55 = (x13 + x54);
    const x56 = (x55 & 0x7ffffffffffff);
    const x57 = cast(u8, (x55 >> 51));
    const x58 = (x12 + cast(u64, x57));
    const x59 = (x11 + x58);
    const x60 = (x10 + x59);
    const x61 = (x9 + x60);
    const x62 = (x8 + x61);
    const x63 = (x7 + x62);
    const x64 = (x63 & 0x7ffffffffffff);
    const x65 = cast(u8, (x63 >> 51));
    const x66 = (x6 + cast(u64, x65));
    const x67 = (x5 + x66);
    const x68 = (x4 + x67);
    const x69 = (x3 + x68);
    const x70 = (x2 + x69);
    const x71 = (x1 + x70);
    out1[0] = x39;
    out1[1] = x47;
    out1[2] = x56;
    out1[3] = x64;
    out1[4] = x71;
}

/// The function relax is the identity function converting from tight field elements to loose field elements.
///
/// Postconditions:
///   out1 = arg1
///
pub fn relax(out1: *LooseFieldElement, arg1: TightFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (arg1[0]);
    const x2 = (arg1[1]);
    const x3 = (arg1[2]);
    const x4 = (arg1[3]);
    const x5 = (arg1[4]);
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function carryScmul121666 multiplies a field element by 121666 and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (121666 * eval arg1) mod m
///
pub fn carryScmul121666(out1: *TightFieldElement, arg1: LooseFieldElement) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u128, 0x1db42) * cast(u128, (arg1[4])));
    const x2 = (cast(u128, 0x1db42) * cast(u128, (arg1[3])));
    const x3 = (cast(u128, 0x1db42) * cast(u128, (arg1[2])));
    const x4 = (cast(u128, 0x1db42) * cast(u128, (arg1[1])));
    const x5 = (cast(u128, 0x1db42) * cast(u128, (arg1[0])));
    const x6 = cast(u64, (x5 >> 51));
    const x7 = cast(u64, (x5 & cast(u128, 0x7ffffffffffff)));
    const x8 = (cast(u128, x6) + x4);
    const x9 = cast(u64, (x8 >> 51));
    const x10 = cast(u64, (x8 & cast(u128, 0x7ffffffffffff)));
    const x11 = (cast(u128, x9) + x3);
    const x12 = cast(u64, (x11 >> 51));
    const x13 = cast(u64, (x11 & cast(u128, 0x7ffffffffffff)));
    const x14 = (cast(u128, x12) + x2);
    const x15 = cast(u64, (x14 >> 51));
    const x16 = cast(u64, (x14 & cast(u128, 0x7ffffffffffff)));
    const x17 = (cast(u128, x15) + x1);
    const x18 = cast(u64, (x17 >> 51));
    const x19 = cast(u64, (x17 & cast(u128, 0x7ffffffffffff)));
    const x20 = (x18 * 0x13);
    const x21 = (x7 + x20);
    const x22 = cast(u1, (x21 >> 51));
    const x23 = (x21 & 0x7ffffffffffff);
    const x24 = (cast(u64, x22) + x10);
    const x25 = cast(u1, (x24 >> 51));
    const x26 = (x24 & 0x7ffffffffffff);
    const x27 = (cast(u64, x25) + x13);
    out1[0] = x23;
    out1[1] = x26;
    out1[2] = x27;
    out1[3] = x16;
    out1[4] = x19;
}
