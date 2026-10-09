const std = @import("std");
const fmt = std.fmt;

fn testVector(comptime fiat: type, expected_s: []const u8) !void {
    std.testing.refAllDecls(fiat);
    // Find the type of the limbs and the size of the serialized representation.
    const repr = switch (@typeInfo(@TypeOf(fiat.fromBytes))) {
        .@"fn" => |f| .{
            .Limbs = switch (@typeInfo(f.param_types[0].?)) {
                .pointer => |p| p.child,
                else => unreachable,
            },
            .bytes = f.param_types[1].?,
        },
        else => unreachable,
    };
    const Limbs = repr.Limbs;
    const Bytes = repr.bytes;
    const encoded_length = @sizeOf(Bytes);

    // Trigger most available functions.
    var as: [encoded_length]u8 = @splat(0x01);
    var a: Limbs = undefined;
    fiat.fromBytes(&a, as);
    if (@hasDecl(fiat, "fromMontgomery")) fiat.fromMontgomery(&a, a);
    var b: Limbs = undefined;
    fiat.opp(&b, a);
    if (@hasDecl(fiat, "carrySquare")) fiat.carrySquare(&a, a) else fiat.square(&a, a);
    if (@hasDecl(fiat, "carryMul")) fiat.carryMul(&b, a, b) else fiat.mul(&b, a, b);
    fiat.add(&b, a, b);
    fiat.sub(&a, b, a);
    if (@hasDecl(fiat, "carry")) fiat.carry(&a, a);
    if (@hasDecl(fiat, "toMontgomery")) fiat.toMontgomery(&a, a);
    fiat.toBytes(&as, a);

    // Check that the result matches the expected one.
    var expected: [as.len]u8 = undefined;
    _ = try fmt.hexToBytes(&expected, expected_s);
    try std.testing.expectEqualSlices(u8, &expected, &as);
}

fn testLooseMulSquare(comptime fiat: type, comptime widths: []const usize, comptime modulus: u512) !void {
    const Limbs = fiat.LooseFieldElement;
    const Word = @typeInfo(Limbs).array.child;
    var state: u64 = 0x243f6a8885a308d3;
    for (0..40) |sample| {
        var a: Limbs = undefined;
        var b: Limbs = undefined;
        var av: u512 = 0;
        var bv: u512 = 0;
        var offset: u9 = 0;
        for (widths, 0..) |bits, i| {
            // Include the inclusive loose bound, one below it, and random limbs.
            const max: Word = @as(Word, 3) << @intCast(bits);
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            a[i] = switch (sample) {
                0 => 0,
                1, 2 => max,
                3 => max - 1,
                else => @intCast(state % (@as(u64, max) + 1)),
            };
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            b[i] = switch (sample) {
                0, 2 => max,
                1 => 0,
                3 => max - 1,
                else => @intCast(state % (@as(u64, max) + 1)),
            };
            av += @as(u512, a[i]) << offset;
            bv += @as(u512, b[i]) << offset;
            offset += @intCast(bits);
        }
        var result: fiat.TightFieldElement = undefined;
        for (0..2) |operation| {
            if (operation == 0) fiat.carryMul(&result, a, b) else fiat.carrySquare(&result, a);
            var actual: u512 = 0;
            offset = 0;
            for (widths, 0..) |bits, i| {
                try std.testing.expect(result[i] <= @as(Word, 1) << @intCast(bits));
                actual += @as(u512, result[i]) << offset;
                offset += @intCast(bits);
            }
            const other = if (operation == 0) bv else av;
            try std.testing.expectEqual(((av % modulus) * (other % modulus)) % modulus, actual % modulus);
        }
    }
}

test "unsaturated carry bounds" {
    const poly = (@as(u512, 1) << 130) - 5;
    try testLooseMulSquare(@import("poly1305_64.zig"), &.{ 44, 43, 43 }, poly);
    try testLooseMulSquare(@import("poly1305_32.zig"), &.{ 26, 26, 26, 26, 26 }, poly);
    const curve = (@as(u512, 1) << 255) - 19;
    try testLooseMulSquare(@import("curve25519_64.zig"), &.{ 51, 51, 51, 51, 51 }, curve);
    try testLooseMulSquare(@import("curve25519_32.zig"), &.{ 26, 25, 26, 25, 26, 25, 26, 25, 26, 25 }, curve);
}

fn testMulSquare(comptime fiat: type, comptime Limbs: type, comptime limb_bits: usize, comptime modulus: u256) !void {
    std.testing.refAllDecls(fiat);
    var a: Limbs = @splat(0);
    var b: Limbs = @splat(0);
    a[0] = 7;
    b[0] = 9;
    var result: Limbs = undefined;
    fiat.mul(&result, a, b);
    var expected: Limbs = @splat(0);
    expected[0] = 63;
    try std.testing.expectEqualSlices(@TypeOf(a[0]), &expected, &result);
    fiat.square(&result, a);
    expected[0] = 49;
    try std.testing.expectEqualSlices(@TypeOf(a[0]), &expected, &result);

    // Compare reduction and carry chains with an independent wide-integer oracle.
    const mask: u512 = (@as(u512, 1) << limb_bits) - 1;
    var state: u64 = 0x243f6a8885a308d3;
    for (0..36) |sample| {
        var av: u256 = 0;
        var bv: u256 = 0;
        for (0..4) |word| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            av |= @as(u256, state) << @intCast(word * 64);
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            bv |= @as(u256, state) << @intCast(word * 64);
        }
        av = switch (sample) {
            0 => modulus - 1,
            1 => modulus - 2,
            2 => 0,
            3 => 1,
            else => av % modulus,
        };
        bv = switch (sample) {
            0, 2, 3 => modulus - 1,
            1 => 2,
            else => bv % modulus,
        };
        for (0..a.len) |i| {
            a[i] = @intCast((@as(u512, av) >> @intCast(i * limb_bits)) & mask);
            b[i] = @intCast((@as(u512, bv) >> @intCast(i * limb_bits)) & mask);
        }
        fiat.mul(&result, a, b);
        var actual: u512 = 0;
        for (result, 0..) |limb, i| actual += @as(u512, limb) << @intCast(i * limb_bits);
        try std.testing.expectEqual((@as(u512, av) * bv) % modulus, actual % modulus);
        fiat.square(&result, a);
        actual = 0;
        for (result, 0..) |limb, i| actual += @as(u512, limb) << @intCast(i * limb_bits);
        try std.testing.expectEqual((@as(u512, av) * av) % modulus, actual % modulus);
    }
}

test "secp256k1_dettman" {
    const modulus = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f;
    try testMulSquare(@import("secp256k1_dettman_32.zig"), [10]u32, 26, modulus);
    try testMulSquare(@import("secp256k1_dettman_64.zig"), [5]u64, 52, modulus);
}

test "curve25519_solinas" {
    const modulus = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    try testMulSquare(@import("curve25519_solinas_64.zig"), [4]u64, 64, modulus);
}

fn testInversion(comptime fiat: type, comptime prime_bits: usize) !void {
    const Limbs = @typeInfo(@typeInfo(@TypeOf(fiat.fromBytes)).@"fn".param_types[0].?).pointer.child;
    const XLimbs = @typeInfo(@typeInfo(@TypeOf(fiat.msat)).@"fn".param_types[0].?).pointer.child;
    const Word = @typeInfo(Limbs).array.child;
    const iterations = (49 * prime_bits + if (prime_bits < 46) 80 else 57) / 17;
    var one: Limbs = undefined;
    fiat.setOne(&one);
    for ([_]Word{ 2, 3, 255 }) |value| {
        var a: Limbs = @splat(0);
        a[0] = value;
        var g: XLimbs = @splat(0);
        g[0] = value;
        fiat.toMontgomery(&a, a);
        var d: Word = 1;
        var f: XLimbs = undefined;
        fiat.msat(&f);
        var r = one;
        var v: Limbs = @splat(0);
        for (0..iterations) |_| {
            fiat.divstep(&d, &f, &g, &v, &r, d, f, g, v, r);
        }
        var negative_v: Limbs = undefined;
        fiat.opp(&negative_v, v);
        fiat.selectznz(&v, @truncate(f[f.len - 1] >> (@bitSizeOf(Word) - 1)), v, negative_v);
        var precomp: Limbs = undefined;
        fiat.divstepPrecomp(&precomp);
        var inverse: Limbs = undefined;
        fiat.mul(&inverse, v, precomp);
        var product: Limbs = undefined;
        fiat.mul(&product, a, inverse);
        try std.testing.expectEqualSlices(Word, &one, &product);
    }
}

test "Montgomery inversion using divstep" {
    try testInversion(@import("p224_32.zig"), 224);
    try testInversion(@import("p224_64.zig"), 224);
    try testInversion(@import("p256_32.zig"), 256);
    try testInversion(@import("p256_64.zig"), 256);
    try testInversion(@import("p384_32.zig"), 384);
    try testInversion(@import("p384_64.zig"), 384);
}

test "curve25519" {
    const expected = "ecb7120fadeccd50753ba3ac57a4922254279cb26ac4bf5c9b7bfd20e64c557f";
    try testVector(@import("curve25519_32.zig"), expected);
    try testVector(@import("curve25519_64.zig"), expected);
}

test "p256" {
    const expected = "aee41f6077662dccf5aaebb7f4c4acab16ef34e8baacbdeddaa8db720b82527d";
    try testVector(@import("p256_32.zig"), expected);
    try testVector(@import("p256_64.zig"), expected);
}

test "p384" {
    const expected = "bec9b37c6d3f51a25a0fecf036c9753d5bb5fd347a5ee40bf7a51e61ae0b810e5b580c77a966ac7ac3b43e6111be49b4";
    try testVector(@import("p384_64.zig"), expected);
}

test "p448_solinas" {
    const expected = "8710971b9e1e9d19940c83f769da48b51f88ee52b51574d02a83d92d08e4bb906231fdc58b4e0ecb843bef9f4df89f44e68420b94ee170fd";
    try testVector(@import("p448_solinas_64.zig"), expected);
}

test "p521" {
    const expected = "beecda88f62311be2a5743ef5a86711c87b19b45afd8c16ad3fbe38bf31a02a90f361cc2274d32d73b6044e84b6f52f5577a5cfe5f81620364846404648362016000";
    try testVector(@import("p521_64.zig"), expected);
}

test "poly1305" {
    const expected = "cc944af0850b81e63b81b6dbf0f5eacf00";
    try testVector(@import("poly1305_32.zig"), expected);
    try testVector(@import("poly1305_64.zig"), expected);
}

test "secp256k1_montgomery" {
    const expected = "aaa4b177db43ac4d443d0171c3bd2ec9db6c0bf91c1941217b81d250614324dc";
    try testVector(@import("secp256k1_montgomery_64.zig"), expected);
}

test "sm2" {
    const expected = "e8ebc77c1c0a46d06f64f1155a55c4a7f98f6a896f584433def06a4cd9bcb3be";
    try testVector(@import("sm2_32.zig"), expected);
    try testVector(@import("sm2_64.zig"), expected);
}

test "sm2scalar" {
    const expected = "d2b9c5b06df4aab19daec578107eaf2a0c38f57f7483f6f24cc6dea78ac89a1f";
    try testVector(@import("sm2_scalar_32.zig"), expected);
    try testVector(@import("sm2_scalar_64.zig"), expected);
}

test "curve25519_scalar_32" {
    try testVector(@import("curve25519_scalar_32.zig"), "dca429964c0fea69c663ebdea95ea1a655642f111a725f5c9a576ae8ccbcf00e");
}

test "curve25519_scalar_64" {
    try testVector(@import("curve25519_scalar_64.zig"), "dca429964c0fea69c663ebdea95ea1a655642f111a725f5c9a576ae8ccbcf00e");
}

test "p224_32" {
    try testVector(@import("p224_32.zig"), "8c25cc7f1690ec2b8c0db073bc0859adfb4386c2198c19c260f57f00");
}

test "p224_64" {
    try testVector(@import("p224_64.zig"), "13d472eea599c935a923a52d73da3380e96f13d473f24f8cb7d1dad2");
}

test "p256_scalar_32" {
    try testVector(@import("p256_scalar_32.zig"), "473cd9e0ab06d3208afb5695394009fa5df2124b270ee4b74f368d38737c776d");
}

test "p256_scalar_64" {
    try testVector(@import("p256_scalar_64.zig"), "473cd9e0ab06d3208afb5695394009fa5df2124b270ee4b74f368d38737c776d");
}

test "p384_32" {
    try testVector(@import("p384_32.zig"), "bec9b37c6d3f51a25a0fecf036c9753d5bb5fd347a5ee40bf7a51e61ae0b810e5b580c77a966ac7ac3b43e6111be49b4");
}

test "p384_scalar_32" {
    try testVector(@import("p384_scalar_32.zig"), "15bbcb4b7e5209e20568641abf812a3f2be764a223f07c0154a9a9b8f6e71c69d81f61806be7d8d4cff47c551ea96aa8");
}

test "p384_scalar_64" {
    try testVector(@import("p384_scalar_64.zig"), "15bbcb4b7e5209e20568641abf812a3f2be764a223f07c0154a9a9b8f6e71c69d81f61806be7d8d4cff47c551ea96aa8");
}

test "p434_64" {
    try testVector(@import("p434_64.zig"), "c046169d43295b7cd74fb1f892d592714edba38d03e2b4dd6a2dbf5453b818c29cf029543980e1c52794debdddf85bc727bed34e0ae700");
}

test "p448_solinas_32" {
    try testVector(@import("p448_solinas_32.zig"), "8710971b9e1e9d19940c83f769da48b51f88ee52b51574d02a83d92d08e4bb906231fdc58b4e0ecb843bef9f4df89f44e68420b94ee170fd");
}

test "p521_32" {
    try testVector(@import("p521_32.zig"), "beecda88f62311be2a5743ef5a86711c87b19b45afd8c16ad3fbe38bf31a02a90f361cc2274d32d73b6044e84b6f52f5577a5cfe5f81620364846404648362016000");
}

test "secp256k1_montgomery_32" {
    try testVector(@import("secp256k1_montgomery_32.zig"), "aaa4b177db43ac4d443d0171c3bd2ec9db6c0bf91c1941217b81d250614324dc");
}

test "secp256k1_montgomery_scalar_32" {
    try testVector(@import("secp256k1_montgomery_scalar_32.zig"), "13415ae7d2b7f5f96698eeaa492cdea5aae4057bea3aefc1c1bbf9c7846d0bc7");
}

test "secp256k1_montgomery_scalar_64" {
    try testVector(@import("secp256k1_montgomery_scalar_64.zig"), "13415ae7d2b7f5f96698eeaa492cdea5aae4057bea3aefc1c1bbf9c7846d0bc7");
}
