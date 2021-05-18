// Autogenerated: 'src/ExtractionOCaml/unsaturated_solinas' --lang Zig --internal-static --public-function-case camelCase --private-function-case camelCase --no-prefix-fiat --package-name poly1305 '' 64 3 '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes relax
// curve description (via package name): poly1305
// machine_wordsize = 64 (from "64")
// requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes, relax
// n = 3 (from "3")
// s-c = 2^130 - [(1, 5)] (from "2^130 - 5")
// tight_bounds_multiplier = 1 (from "")
//
// Computed values:
//   carry_chain = [0, 1, 2, 0, 1]
//   eval z = z[0] + (z[1] << 44) + (z[2] << 87)
//   bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128)
//   balance = [0x1ffffffffff6, 0xffffffffffe, 0xffffffffffe]

const std = @import("std");
const cast = std.meta.cast;
const mode = std.builtin.mode; // Checked arithmetic is disabled in non-debug modes to avoid side channels

// The type loose_field_element is a field element with loose bounds.
// Bounds: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]]
pub const loose_field_element = [3]u64;

// The type tight_field_element is a field element with tight bounds.
// Bounds: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]]
pub const tight_field_element = [3]u64;

/// The function addcarryxU44 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^44
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^44⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xfffffffffff]
///   arg3: [0x0 ~> 0xfffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xfffffffffff]
///   out2: [0x0 ~> 0x1]
fn addcarryxU44(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((cast(u64, arg1) + arg2) + arg3);
    const x2 = (x1 & 0xfffffffffff);
    const x3 = cast(u1, (x1 >> 44));
    out1.* = x2;
    out2.* = x3;
}

/// The function subborrowxU44 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^44
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^44⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xfffffffffff]
///   arg3: [0x0 ~> 0xfffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xfffffffffff]
///   out2: [0x0 ~> 0x1]
fn subborrowxU44(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = cast(i64, (cast(i128, cast(i64, (cast(i128, arg2) - cast(i128, arg1)))) - cast(i128, arg3)));
    const x2 = cast(i1, (x1 >> 44));
    const x3 = cast(u64, (cast(i128, x1) & cast(i128, 0xfffffffffff)));
    out1.* = x3;
    out2.* = cast(u1, (cast(i2, 0x0) - cast(i2, x2)));
}

/// The function addcarryxU43 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^43
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^43⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffff]
///   out2: [0x0 ~> 0x1]
fn addcarryxU43(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((cast(u64, arg1) + arg2) + arg3);
    const x2 = (x1 & 0x7ffffffffff);
    const x3 = cast(u1, (x1 >> 43));
    out1.* = x2;
    out2.* = x3;
}

/// The function subborrowxU43 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^43
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^43⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffff]
///   out2: [0x0 ~> 0x1]
fn subborrowxU43(out1: *u64, out2: *u1, arg1: u1, arg2: u64, arg3: u64) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = cast(i64, (cast(i128, cast(i64, (cast(i128, arg2) - cast(i128, arg1)))) - cast(i128, arg3)));
    const x2 = cast(i1, (x1 >> 43));
    const x3 = cast(u64, (cast(i128, x1) & cast(i128, 0x7ffffffffff)));
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
fn cmovznzU64(out1: *u64, arg1: u1, arg2: u64, arg3: u64) callconv(.Inline) void {
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
pub fn carryMul(out1: *tight_field_element, arg1: loose_field_element, arg2: loose_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u128, (arg1[2])) * cast(u128, ((arg2[2]) * 0x5)));
    const x2 = (cast(u128, (arg1[2])) * cast(u128, ((arg2[1]) * 0xa)));
    const x3 = (cast(u128, (arg1[1])) * cast(u128, ((arg2[2]) * 0xa)));
    const x4 = (cast(u128, (arg1[2])) * cast(u128, (arg2[0])));
    const x5 = (cast(u128, (arg1[1])) * cast(u128, ((arg2[1]) * 0x2)));
    const x6 = (cast(u128, (arg1[1])) * cast(u128, (arg2[0])));
    const x7 = (cast(u128, (arg1[0])) * cast(u128, (arg2[2])));
    const x8 = (cast(u128, (arg1[0])) * cast(u128, (arg2[1])));
    const x9 = (cast(u128, (arg1[0])) * cast(u128, (arg2[0])));
    const x10 = (x9 + (x3 + x2));
    const x11 = cast(u64, (x10 >> 44));
    const x12 = cast(u64, (x10 & cast(u128, 0xfffffffffff)));
    const x13 = (x7 + (x5 + x4));
    const x14 = (x8 + (x6 + x1));
    const x15 = (cast(u128, x11) + x14);
    const x16 = cast(u64, (x15 >> 43));
    const x17 = cast(u64, (x15 & cast(u128, 0x7ffffffffff)));
    const x18 = (cast(u128, x16) + x13);
    const x19 = cast(u64, (x18 >> 43));
    const x20 = cast(u64, (x18 & cast(u128, 0x7ffffffffff)));
    const x21 = (x19 * 0x5);
    const x22 = (x12 + x21);
    const x23 = (x22 >> 44);
    const x24 = (x22 & 0xfffffffffff);
    const x25 = (x23 + x17);
    const x26 = cast(u1, (x25 >> 43));
    const x27 = (x25 & 0x7ffffffffff);
    const x28 = (cast(u64, x26) + x20);
    out1[0] = x24;
    out1[1] = x27;
    out1[2] = x28;
}

/// The function carrySquare squares a field element and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg1) mod m
///
pub fn carrySquare(out1: *tight_field_element, arg1: loose_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((arg1[2]) * 0x5);
    const x2 = (x1 * 0x2);
    const x3 = ((arg1[2]) * 0x2);
    const x4 = ((arg1[1]) * 0x2);
    const x5 = (cast(u128, (arg1[2])) * cast(u128, x1));
    const x6 = (cast(u128, (arg1[1])) * cast(u128, (x2 * 0x2)));
    const x7 = (cast(u128, (arg1[1])) * cast(u128, ((arg1[1]) * 0x2)));
    const x8 = (cast(u128, (arg1[0])) * cast(u128, x3));
    const x9 = (cast(u128, (arg1[0])) * cast(u128, x4));
    const x10 = (cast(u128, (arg1[0])) * cast(u128, (arg1[0])));
    const x11 = (x10 + x6);
    const x12 = cast(u64, (x11 >> 44));
    const x13 = cast(u64, (x11 & cast(u128, 0xfffffffffff)));
    const x14 = (x8 + x7);
    const x15 = (x9 + x5);
    const x16 = (cast(u128, x12) + x15);
    const x17 = cast(u64, (x16 >> 43));
    const x18 = cast(u64, (x16 & cast(u128, 0x7ffffffffff)));
    const x19 = (cast(u128, x17) + x14);
    const x20 = cast(u64, (x19 >> 43));
    const x21 = cast(u64, (x19 & cast(u128, 0x7ffffffffff)));
    const x22 = (x20 * 0x5);
    const x23 = (x13 + x22);
    const x24 = (x23 >> 44);
    const x25 = (x23 & 0xfffffffffff);
    const x26 = (x24 + x18);
    const x27 = cast(u1, (x26 >> 43));
    const x28 = (x26 & 0x7ffffffffff);
    const x29 = (cast(u64, x27) + x21);
    out1[0] = x25;
    out1[1] = x28;
    out1[2] = x29;
}

/// The function carry reduces a field element.
///
/// Postconditions:
///   eval out1 mod m = eval arg1 mod m
///
pub fn carry(out1: *tight_field_element, arg1: loose_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (arg1[0]);
    const x2 = ((x1 >> 44) + (arg1[1]));
    const x3 = ((x2 >> 43) + (arg1[2]));
    const x4 = ((x1 & 0xfffffffffff) + ((x3 >> 43) * 0x5));
    const x5 = (cast(u64, cast(u1, (x4 >> 44))) + (x2 & 0x7ffffffffff));
    const x6 = (x4 & 0xfffffffffff);
    const x7 = (x5 & 0x7ffffffffff);
    const x8 = (cast(u64, cast(u1, (x5 >> 43))) + (x3 & 0x7ffffffffff));
    out1[0] = x6;
    out1[1] = x7;
    out1[2] = x8;
}

/// The function add adds two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 + eval arg2) mod m
///
pub fn add(out1: *loose_field_element, arg1: tight_field_element, arg2: tight_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((arg1[0]) + (arg2[0]));
    const x2 = ((arg1[1]) + (arg2[1]));
    const x3 = ((arg1[2]) + (arg2[2]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
}

/// The function sub subtracts two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 - eval arg2) mod m
///
pub fn sub(out1: *loose_field_element, arg1: tight_field_element, arg2: tight_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((0x1ffffffffff6 + (arg1[0])) - (arg2[0]));
    const x2 = ((0xffffffffffe + (arg1[1])) - (arg2[1]));
    const x3 = ((0xffffffffffe + (arg1[2])) - (arg2[2]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
}

/// The function opp negates a field element.
///
/// Postconditions:
///   eval out1 mod m = -eval arg1 mod m
///
pub fn opp(out1: *loose_field_element, arg1: tight_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (0x1ffffffffff6 - (arg1[0]));
    const x2 = (0xffffffffffe - (arg1[1]));
    const x3 = (0xffffffffffe - (arg1[2]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
}

/// The function selectznz is a multi-limb conditional select.
///
/// Postconditions:
///   eval out1 = (if arg1 = 0 then eval arg2 else eval arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
///   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
pub fn selectznz(out1: *[3]u64, arg1: u1, arg2: [3]u64, arg3: [3]u64) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u64 = undefined;
    cmovznzU64(&x1, arg1, (arg2[0]), (arg3[0]));
    var x2: u64 = undefined;
    cmovznzU64(&x2, arg1, (arg2[1]), (arg3[1]));
    var x3: u64 = undefined;
    cmovznzU64(&x3, arg1, (arg2[2]), (arg3[2]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
}

/// The function toBytes serializes a field element to bytes in little-endian order.
///
/// Postconditions:
///   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16]
///
/// Output Bounds:
///   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
pub fn toBytes(out1: *[17]u8, arg1: tight_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u64 = undefined;
    var x2: u1 = undefined;
    subborrowxU44(&x1, &x2, 0x0, (arg1[0]), 0xffffffffffb);
    var x3: u64 = undefined;
    var x4: u1 = undefined;
    subborrowxU43(&x3, &x4, x2, (arg1[1]), 0x7ffffffffff);
    var x5: u64 = undefined;
    var x6: u1 = undefined;
    subborrowxU43(&x5, &x6, x4, (arg1[2]), 0x7ffffffffff);
    var x7: u64 = undefined;
    cmovznzU64(&x7, x6, cast(u64, 0x0), 0xffffffffffffffff);
    var x8: u64 = undefined;
    var x9: u1 = undefined;
    addcarryxU44(&x8, &x9, 0x0, x1, (x7 & 0xffffffffffb));
    var x10: u64 = undefined;
    var x11: u1 = undefined;
    addcarryxU43(&x10, &x11, x9, x3, (x7 & 0x7ffffffffff));
    var x12: u64 = undefined;
    var x13: u1 = undefined;
    addcarryxU43(&x12, &x13, x11, x5, (x7 & 0x7ffffffffff));
    const x14 = (x12 << 7);
    const x15 = (x10 << 4);
    const x16 = cast(u8, (x8 & cast(u64, 0xff)));
    const x17 = (x8 >> 8);
    const x18 = cast(u8, (x17 & cast(u64, 0xff)));
    const x19 = (x17 >> 8);
    const x20 = cast(u8, (x19 & cast(u64, 0xff)));
    const x21 = (x19 >> 8);
    const x22 = cast(u8, (x21 & cast(u64, 0xff)));
    const x23 = (x21 >> 8);
    const x24 = cast(u8, (x23 & cast(u64, 0xff)));
    const x25 = cast(u8, (x23 >> 8));
    const x26 = (x15 + cast(u64, x25));
    const x27 = cast(u8, (x26 & cast(u64, 0xff)));
    const x28 = (x26 >> 8);
    const x29 = cast(u8, (x28 & cast(u64, 0xff)));
    const x30 = (x28 >> 8);
    const x31 = cast(u8, (x30 & cast(u64, 0xff)));
    const x32 = (x30 >> 8);
    const x33 = cast(u8, (x32 & cast(u64, 0xff)));
    const x34 = (x32 >> 8);
    const x35 = cast(u8, (x34 & cast(u64, 0xff)));
    const x36 = cast(u8, (x34 >> 8));
    const x37 = (x14 + cast(u64, x36));
    const x38 = cast(u8, (x37 & cast(u64, 0xff)));
    const x39 = (x37 >> 8);
    const x40 = cast(u8, (x39 & cast(u64, 0xff)));
    const x41 = (x39 >> 8);
    const x42 = cast(u8, (x41 & cast(u64, 0xff)));
    const x43 = (x41 >> 8);
    const x44 = cast(u8, (x43 & cast(u64, 0xff)));
    const x45 = (x43 >> 8);
    const x46 = cast(u8, (x45 & cast(u64, 0xff)));
    const x47 = (x45 >> 8);
    const x48 = cast(u8, (x47 & cast(u64, 0xff)));
    const x49 = cast(u8, (x47 >> 8));
    out1[0] = x16;
    out1[1] = x18;
    out1[2] = x20;
    out1[3] = x22;
    out1[4] = x24;
    out1[5] = x27;
    out1[6] = x29;
    out1[7] = x31;
    out1[8] = x33;
    out1[9] = x35;
    out1[10] = x38;
    out1[11] = x40;
    out1[12] = x42;
    out1[13] = x44;
    out1[14] = x46;
    out1[15] = x48;
    out1[16] = x49;
}

/// The function fromBytes deserializes a field element from bytes in little-endian order.
///
/// Postconditions:
///   eval out1 mod m = bytes_eval arg1 mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
pub fn fromBytes(out1: *tight_field_element, arg1: [17]u8) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u64, (arg1[16])) << 41);
    const x2 = (cast(u64, (arg1[15])) << 33);
    const x3 = (cast(u64, (arg1[14])) << 25);
    const x4 = (cast(u64, (arg1[13])) << 17);
    const x5 = (cast(u64, (arg1[12])) << 9);
    const x6 = (cast(u64, (arg1[11])) * cast(u64, 0x2));
    const x7 = (cast(u64, (arg1[10])) << 36);
    const x8 = (cast(u64, (arg1[9])) << 28);
    const x9 = (cast(u64, (arg1[8])) << 20);
    const x10 = (cast(u64, (arg1[7])) << 12);
    const x11 = (cast(u64, (arg1[6])) << 4);
    const x12 = (cast(u64, (arg1[5])) << 40);
    const x13 = (cast(u64, (arg1[4])) << 32);
    const x14 = (cast(u64, (arg1[3])) << 24);
    const x15 = (cast(u64, (arg1[2])) << 16);
    const x16 = (cast(u64, (arg1[1])) << 8);
    const x17 = (arg1[0]);
    const x18 = (x16 + cast(u64, x17));
    const x19 = (x15 + x18);
    const x20 = (x14 + x19);
    const x21 = (x13 + x20);
    const x22 = (x12 + x21);
    const x23 = (x22 & 0xfffffffffff);
    const x24 = cast(u8, (x22 >> 44));
    const x25 = (x11 + cast(u64, x24));
    const x26 = (x10 + x25);
    const x27 = (x9 + x26);
    const x28 = (x8 + x27);
    const x29 = (x7 + x28);
    const x30 = (x29 & 0x7ffffffffff);
    const x31 = cast(u1, (x29 >> 43));
    const x32 = (x6 + cast(u64, x31));
    const x33 = (x5 + x32);
    const x34 = (x4 + x33);
    const x35 = (x3 + x34);
    const x36 = (x2 + x35);
    const x37 = (x1 + x36);
    out1[0] = x23;
    out1[1] = x30;
    out1[2] = x37;
}

/// The function relax is the identity function converting from tight field elements to loose field elements.
///
/// Postconditions:
///   out1 = arg1
///
pub fn relax(out1: *loose_field_element, arg1: tight_field_element) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (arg1[0]);
    const x2 = (arg1[1]);
    const x3 = (arg1[2]);
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
}
