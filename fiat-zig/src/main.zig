const std = @import("std");
const fmt = std.fmt;

fn testVector(comptime fiat: type, expected_s: []const u8) !void {
    // Find the type of the limbs and the size of the serialized representation.
    const repr = switch (@typeInfo(@TypeOf(fiat.fromBytes))) {
        .Fn => |f| .{
            .Limbs = switch (@typeInfo(f.args[0].arg_type.?)) {
                .Pointer => |p| p.child,
                else => unreachable,
            },
            .Bytes = f.args[1].arg_type.?,
        },
        else => unreachable,
    };
    const Limbs = repr.Limbs;
    const Bytes = repr.Bytes;
    const encoded_length = @sizeOf(Bytes);

    // Trigger most available functions.
    var as = [_]u8{0x01} ** encoded_length;
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
    std.debug.print("> {s}\n", .{fmt.fmtSliceHexLower(&as)});
    try std.testing.expectEqualSlices(u8, &expected, &as);
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

test "secp256k1" {
    const expected = "aaa4b177db43ac4d443d0171c3bd2ec9db6c0bf91c1941217b81d250614324dc";
    try testVector(@import("secp256k1_64.zig"), expected);
}
