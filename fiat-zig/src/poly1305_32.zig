// Autogenerated: 'src/ExtractionOCaml/unsaturated_solinas' --lang Zig --internal-static --public-function-case camelCase --private-function-case camelCase --no-prefix-fiat --package-name poly1305 '' 32 '(auto)' '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes
// curve description (via package name): poly1305
// machine_wordsize = 32 (from "32")
// requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes
// n = 5 (from "(auto)")
// s-c = 2^130 - [(1, 5)] (from "2^130 - 5")
// tight_bounds_multiplier = 1 (from "")
//
// Computed values:
//   carry_chain = [0, 1, 2, 3, 4, 0, 1]
//   eval z = z[0] + (z[1] << 26) + (z[2] << 52) + (z[3] << 78) + (z[4] << 104)
//   bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128)
//   balance = [0x7fffff6, 0x7fffffe, 0x7fffffe, 0x7fffffe, 0x7fffffe]

const std = @import("std");
const cast = std.meta.cast;
const mode = std.builtin.mode; // Checked arithmetic is disabled in non-debug modes to avoid side channels

/// The function addcarryxU26 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^26
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^26⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x3ffffff]
///   arg3: [0x0 ~> 0x3ffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x3ffffff]
///   out2: [0x0 ~> 0x1]
fn addcarryxU26(out1: *u32, out2: *u1, arg1: u1, arg2: u32, arg3: u32) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((cast(u32, arg1) + arg2) + arg3);
    const x2 = (x1 & 0x3ffffff);
    const x3 = cast(u1, (x1 >> 26));
    out1.* = x2;
    out2.* = x3;
}

/// The function subborrowxU26 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^26
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^26⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x3ffffff]
///   arg3: [0x0 ~> 0x3ffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x3ffffff]
///   out2: [0x0 ~> 0x1]
fn subborrowxU26(out1: *u32, out2: *u1, arg1: u1, arg2: u32, arg3: u32) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = cast(i32, (cast(i64, cast(i32, (cast(i64, arg2) - cast(i64, arg1)))) - cast(i64, arg3)));
    const x2 = cast(i1, (x1 >> 26));
    const x3 = cast(u32, (cast(i64, x1) & cast(i64, 0x3ffffff)));
    out1.* = x3;
    out2.* = cast(u1, (cast(i2, 0x0) - cast(i2, x2)));
}

/// The function cmovznzU32 is a single-word conditional move.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xffffffff]
///   arg3: [0x0 ~> 0xffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xffffffff]
fn cmovznzU32(out1: *u32, arg1: u1, arg2: u32, arg3: u32) callconv(.Inline) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (~(~arg1));
    const x2 = cast(u32, (cast(i64, cast(i1, (cast(i2, 0x0) - cast(i2, x1)))) & cast(i64, 0xffffffff)));
    const x3 = ((x2 & arg3) | ((~x2) & arg2));
    out1.* = x3;
}

/// The function carryMul multiplies two field elements and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg2) mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
///   arg2: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
pub fn carryMul(out1: *[5]u32, arg1: [5]u32, arg2: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u64, (arg1[4])) * cast(u64, ((arg2[4]) * 0x5)));
    const x2 = (cast(u64, (arg1[4])) * cast(u64, ((arg2[3]) * 0x5)));
    const x3 = (cast(u64, (arg1[4])) * cast(u64, ((arg2[2]) * 0x5)));
    const x4 = (cast(u64, (arg1[4])) * cast(u64, ((arg2[1]) * 0x5)));
    const x5 = (cast(u64, (arg1[3])) * cast(u64, ((arg2[4]) * 0x5)));
    const x6 = (cast(u64, (arg1[3])) * cast(u64, ((arg2[3]) * 0x5)));
    const x7 = (cast(u64, (arg1[3])) * cast(u64, ((arg2[2]) * 0x5)));
    const x8 = (cast(u64, (arg1[2])) * cast(u64, ((arg2[4]) * 0x5)));
    const x9 = (cast(u64, (arg1[2])) * cast(u64, ((arg2[3]) * 0x5)));
    const x10 = (cast(u64, (arg1[1])) * cast(u64, ((arg2[4]) * 0x5)));
    const x11 = (cast(u64, (arg1[4])) * cast(u64, (arg2[0])));
    const x12 = (cast(u64, (arg1[3])) * cast(u64, (arg2[1])));
    const x13 = (cast(u64, (arg1[3])) * cast(u64, (arg2[0])));
    const x14 = (cast(u64, (arg1[2])) * cast(u64, (arg2[2])));
    const x15 = (cast(u64, (arg1[2])) * cast(u64, (arg2[1])));
    const x16 = (cast(u64, (arg1[2])) * cast(u64, (arg2[0])));
    const x17 = (cast(u64, (arg1[1])) * cast(u64, (arg2[3])));
    const x18 = (cast(u64, (arg1[1])) * cast(u64, (arg2[2])));
    const x19 = (cast(u64, (arg1[1])) * cast(u64, (arg2[1])));
    const x20 = (cast(u64, (arg1[1])) * cast(u64, (arg2[0])));
    const x21 = (cast(u64, (arg1[0])) * cast(u64, (arg2[4])));
    const x22 = (cast(u64, (arg1[0])) * cast(u64, (arg2[3])));
    const x23 = (cast(u64, (arg1[0])) * cast(u64, (arg2[2])));
    const x24 = (cast(u64, (arg1[0])) * cast(u64, (arg2[1])));
    const x25 = (cast(u64, (arg1[0])) * cast(u64, (arg2[0])));
    const x26 = (x25 + (x10 + (x9 + (x7 + x4))));
    const x27 = (x26 >> 26);
    const x28 = cast(u32, (x26 & cast(u64, 0x3ffffff)));
    const x29 = (x21 + (x17 + (x14 + (x12 + x11))));
    const x30 = (x22 + (x18 + (x15 + (x13 + x1))));
    const x31 = (x23 + (x19 + (x16 + (x5 + x2))));
    const x32 = (x24 + (x20 + (x8 + (x6 + x3))));
    const x33 = (x27 + x32);
    const x34 = (x33 >> 26);
    const x35 = cast(u32, (x33 & cast(u64, 0x3ffffff)));
    const x36 = (x34 + x31);
    const x37 = (x36 >> 26);
    const x38 = cast(u32, (x36 & cast(u64, 0x3ffffff)));
    const x39 = (x37 + x30);
    const x40 = (x39 >> 26);
    const x41 = cast(u32, (x39 & cast(u64, 0x3ffffff)));
    const x42 = (x40 + x29);
    const x43 = cast(u32, (x42 >> 26));
    const x44 = cast(u32, (x42 & cast(u64, 0x3ffffff)));
    const x45 = (cast(u64, x43) * cast(u64, 0x5));
    const x46 = (cast(u64, x28) + x45);
    const x47 = cast(u32, (x46 >> 26));
    const x48 = cast(u32, (x46 & cast(u64, 0x3ffffff)));
    const x49 = (x47 + x35);
    const x50 = cast(u1, (x49 >> 26));
    const x51 = (x49 & 0x3ffffff);
    const x52 = (cast(u32, x50) + x38);
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
/// Input Bounds:
///   arg1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
pub fn carrySquare(out1: *[5]u32, arg1: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((arg1[4]) * 0x5);
    const x2 = (x1 * 0x2);
    const x3 = ((arg1[4]) * 0x2);
    const x4 = ((arg1[3]) * 0x5);
    const x5 = (x4 * 0x2);
    const x6 = ((arg1[3]) * 0x2);
    const x7 = ((arg1[2]) * 0x2);
    const x8 = ((arg1[1]) * 0x2);
    const x9 = (cast(u64, (arg1[4])) * cast(u64, x1));
    const x10 = (cast(u64, (arg1[3])) * cast(u64, x2));
    const x11 = (cast(u64, (arg1[3])) * cast(u64, x4));
    const x12 = (cast(u64, (arg1[2])) * cast(u64, x2));
    const x13 = (cast(u64, (arg1[2])) * cast(u64, x5));
    const x14 = (cast(u64, (arg1[2])) * cast(u64, (arg1[2])));
    const x15 = (cast(u64, (arg1[1])) * cast(u64, x2));
    const x16 = (cast(u64, (arg1[1])) * cast(u64, x6));
    const x17 = (cast(u64, (arg1[1])) * cast(u64, x7));
    const x18 = (cast(u64, (arg1[1])) * cast(u64, (arg1[1])));
    const x19 = (cast(u64, (arg1[0])) * cast(u64, x3));
    const x20 = (cast(u64, (arg1[0])) * cast(u64, x6));
    const x21 = (cast(u64, (arg1[0])) * cast(u64, x7));
    const x22 = (cast(u64, (arg1[0])) * cast(u64, x8));
    const x23 = (cast(u64, (arg1[0])) * cast(u64, (arg1[0])));
    const x24 = (x23 + (x15 + x13));
    const x25 = (x24 >> 26);
    const x26 = cast(u32, (x24 & cast(u64, 0x3ffffff)));
    const x27 = (x19 + (x16 + x14));
    const x28 = (x20 + (x17 + x9));
    const x29 = (x21 + (x18 + x10));
    const x30 = (x22 + (x12 + x11));
    const x31 = (x25 + x30);
    const x32 = (x31 >> 26);
    const x33 = cast(u32, (x31 & cast(u64, 0x3ffffff)));
    const x34 = (x32 + x29);
    const x35 = (x34 >> 26);
    const x36 = cast(u32, (x34 & cast(u64, 0x3ffffff)));
    const x37 = (x35 + x28);
    const x38 = (x37 >> 26);
    const x39 = cast(u32, (x37 & cast(u64, 0x3ffffff)));
    const x40 = (x38 + x27);
    const x41 = cast(u32, (x40 >> 26));
    const x42 = cast(u32, (x40 & cast(u64, 0x3ffffff)));
    const x43 = (cast(u64, x41) * cast(u64, 0x5));
    const x44 = (cast(u64, x26) + x43);
    const x45 = cast(u32, (x44 >> 26));
    const x46 = cast(u32, (x44 & cast(u64, 0x3ffffff)));
    const x47 = (x45 + x33);
    const x48 = cast(u1, (x47 >> 26));
    const x49 = (x47 & 0x3ffffff);
    const x50 = (cast(u32, x48) + x36);
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
/// Input Bounds:
///   arg1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
pub fn carry(out1: *[5]u32, arg1: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (arg1[0]);
    const x2 = ((x1 >> 26) + (arg1[1]));
    const x3 = ((x2 >> 26) + (arg1[2]));
    const x4 = ((x3 >> 26) + (arg1[3]));
    const x5 = ((x4 >> 26) + (arg1[4]));
    const x6 = ((x1 & 0x3ffffff) + ((x5 >> 26) * 0x5));
    const x7 = (cast(u32, cast(u1, (x6 >> 26))) + (x2 & 0x3ffffff));
    const x8 = (x6 & 0x3ffffff);
    const x9 = (x7 & 0x3ffffff);
    const x10 = (cast(u32, cast(u1, (x7 >> 26))) + (x3 & 0x3ffffff));
    const x11 = (x4 & 0x3ffffff);
    const x12 = (x5 & 0x3ffffff);
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
/// Input Bounds:
///   arg1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
///   arg2: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
pub fn add(out1: *[5]u32, arg1: [5]u32, arg2: [5]u32) void {
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
/// Input Bounds:
///   arg1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
///   arg2: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
pub fn sub(out1: *[5]u32, arg1: [5]u32, arg2: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = ((0x7fffff6 + (arg1[0])) - (arg2[0]));
    const x2 = ((0x7fffffe + (arg1[1])) - (arg2[1]));
    const x3 = ((0x7fffffe + (arg1[2])) - (arg2[2]));
    const x4 = ((0x7fffffe + (arg1[3])) - (arg2[3]));
    const x5 = ((0x7fffffe + (arg1[4])) - (arg2[4]));
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
/// Input Bounds:
///   arg1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000], [0x0 ~> 0xc000000]]
pub fn opp(out1: *[5]u32, arg1: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (0x7fffff6 - (arg1[0]));
    const x2 = (0x7fffffe - (arg1[1]));
    const x3 = (0x7fffffe - (arg1[2]));
    const x4 = (0x7fffffe - (arg1[3]));
    const x5 = (0x7fffffe - (arg1[4]));
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
///   arg2: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
///   arg3: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff], [0x0 ~> 0xffffffff]]
pub fn selectznz(out1: *[5]u32, arg1: u1, arg2: [5]u32, arg3: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u32 = undefined;
    cmovznzU32(&x1, arg1, (arg2[0]), (arg3[0]));
    var x2: u32 = undefined;
    cmovznzU32(&x2, arg1, (arg2[1]), (arg3[1]));
    var x3: u32 = undefined;
    cmovznzU32(&x3, arg1, (arg2[2]), (arg3[2]));
    var x4: u32 = undefined;
    cmovznzU32(&x4, arg1, (arg2[3]), (arg3[3]));
    var x5: u32 = undefined;
    cmovznzU32(&x5, arg1, (arg2[4]), (arg3[4]));
    out1[0] = x1;
    out1[1] = x2;
    out1[2] = x3;
    out1[3] = x4;
    out1[4] = x5;
}

/// The function toBytes serializes a field element to bytes in little-endian order.
///
/// Postconditions:
///   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16]
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
pub fn toBytes(out1: *[17]u8, arg1: [5]u32) void {
    @setRuntimeSafety(mode == .Debug);

    var x1: u32 = undefined;
    var x2: u1 = undefined;
    subborrowxU26(&x1, &x2, 0x0, (arg1[0]), 0x3fffffb);
    var x3: u32 = undefined;
    var x4: u1 = undefined;
    subborrowxU26(&x3, &x4, x2, (arg1[1]), 0x3ffffff);
    var x5: u32 = undefined;
    var x6: u1 = undefined;
    subborrowxU26(&x5, &x6, x4, (arg1[2]), 0x3ffffff);
    var x7: u32 = undefined;
    var x8: u1 = undefined;
    subborrowxU26(&x7, &x8, x6, (arg1[3]), 0x3ffffff);
    var x9: u32 = undefined;
    var x10: u1 = undefined;
    subborrowxU26(&x9, &x10, x8, (arg1[4]), 0x3ffffff);
    var x11: u32 = undefined;
    cmovznzU32(&x11, x10, cast(u32, 0x0), 0xffffffff);
    var x12: u32 = undefined;
    var x13: u1 = undefined;
    addcarryxU26(&x12, &x13, 0x0, x1, (x11 & 0x3fffffb));
    var x14: u32 = undefined;
    var x15: u1 = undefined;
    addcarryxU26(&x14, &x15, x13, x3, (x11 & 0x3ffffff));
    var x16: u32 = undefined;
    var x17: u1 = undefined;
    addcarryxU26(&x16, &x17, x15, x5, (x11 & 0x3ffffff));
    var x18: u32 = undefined;
    var x19: u1 = undefined;
    addcarryxU26(&x18, &x19, x17, x7, (x11 & 0x3ffffff));
    var x20: u32 = undefined;
    var x21: u1 = undefined;
    addcarryxU26(&x20, &x21, x19, x9, (x11 & 0x3ffffff));
    const x22 = (x18 << 6);
    const x23 = (x16 << 4);
    const x24 = (x14 << 2);
    const x25 = cast(u8, (x12 & cast(u32, 0xff)));
    const x26 = (x12 >> 8);
    const x27 = cast(u8, (x26 & cast(u32, 0xff)));
    const x28 = (x26 >> 8);
    const x29 = cast(u8, (x28 & cast(u32, 0xff)));
    const x30 = cast(u8, (x28 >> 8));
    const x31 = (x24 + cast(u32, x30));
    const x32 = cast(u8, (x31 & cast(u32, 0xff)));
    const x33 = (x31 >> 8);
    const x34 = cast(u8, (x33 & cast(u32, 0xff)));
    const x35 = (x33 >> 8);
    const x36 = cast(u8, (x35 & cast(u32, 0xff)));
    const x37 = cast(u8, (x35 >> 8));
    const x38 = (x23 + cast(u32, x37));
    const x39 = cast(u8, (x38 & cast(u32, 0xff)));
    const x40 = (x38 >> 8);
    const x41 = cast(u8, (x40 & cast(u32, 0xff)));
    const x42 = (x40 >> 8);
    const x43 = cast(u8, (x42 & cast(u32, 0xff)));
    const x44 = cast(u8, (x42 >> 8));
    const x45 = (x22 + cast(u32, x44));
    const x46 = cast(u8, (x45 & cast(u32, 0xff)));
    const x47 = (x45 >> 8);
    const x48 = cast(u8, (x47 & cast(u32, 0xff)));
    const x49 = (x47 >> 8);
    const x50 = cast(u8, (x49 & cast(u32, 0xff)));
    const x51 = cast(u8, (x49 >> 8));
    const x52 = cast(u8, (x20 & cast(u32, 0xff)));
    const x53 = (x20 >> 8);
    const x54 = cast(u8, (x53 & cast(u32, 0xff)));
    const x55 = (x53 >> 8);
    const x56 = cast(u8, (x55 & cast(u32, 0xff)));
    const x57 = cast(u8, (x55 >> 8));
    out1[0] = x25;
    out1[1] = x27;
    out1[2] = x29;
    out1[3] = x32;
    out1[4] = x34;
    out1[5] = x36;
    out1[6] = x39;
    out1[7] = x41;
    out1[8] = x43;
    out1[9] = x46;
    out1[10] = x48;
    out1[11] = x50;
    out1[12] = x51;
    out1[13] = x52;
    out1[14] = x54;
    out1[15] = x56;
    out1[16] = x57;
}

/// The function fromBytes deserializes a field element from bytes in little-endian order.
///
/// Postconditions:
///   eval out1 mod m = bytes_eval arg1 mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
/// Output Bounds:
///   out1: [[0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000], [0x0 ~> 0x4000000]]
pub fn fromBytes(out1: *[5]u32, arg1: [17]u8) void {
    @setRuntimeSafety(mode == .Debug);

    const x1 = (cast(u32, (arg1[16])) << 24);
    const x2 = (cast(u32, (arg1[15])) << 16);
    const x3 = (cast(u32, (arg1[14])) << 8);
    const x4 = (arg1[13]);
    const x5 = (cast(u32, (arg1[12])) << 18);
    const x6 = (cast(u32, (arg1[11])) << 10);
    const x7 = (cast(u32, (arg1[10])) << 2);
    const x8 = (cast(u32, (arg1[9])) << 20);
    const x9 = (cast(u32, (arg1[8])) << 12);
    const x10 = (cast(u32, (arg1[7])) << 4);
    const x11 = (cast(u32, (arg1[6])) << 22);
    const x12 = (cast(u32, (arg1[5])) << 14);
    const x13 = (cast(u32, (arg1[4])) << 6);
    const x14 = (cast(u32, (arg1[3])) << 24);
    const x15 = (cast(u32, (arg1[2])) << 16);
    const x16 = (cast(u32, (arg1[1])) << 8);
    const x17 = (arg1[0]);
    const x18 = (x16 + cast(u32, x17));
    const x19 = (x15 + x18);
    const x20 = (x14 + x19);
    const x21 = (x20 & 0x3ffffff);
    const x22 = cast(u8, (x20 >> 26));
    const x23 = (x13 + cast(u32, x22));
    const x24 = (x12 + x23);
    const x25 = (x11 + x24);
    const x26 = (x25 & 0x3ffffff);
    const x27 = cast(u8, (x25 >> 26));
    const x28 = (x10 + cast(u32, x27));
    const x29 = (x9 + x28);
    const x30 = (x8 + x29);
    const x31 = (x30 & 0x3ffffff);
    const x32 = cast(u8, (x30 >> 26));
    const x33 = (x7 + cast(u32, x32));
    const x34 = (x6 + x33);
    const x35 = (x5 + x34);
    const x36 = (x3 + cast(u32, x4));
    const x37 = (x2 + x36);
    const x38 = (x1 + x37);
    out1[0] = x21;
    out1[1] = x26;
    out1[2] = x31;
    out1[3] = x35;
    out1[4] = x38;
}
