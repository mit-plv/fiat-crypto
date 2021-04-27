const std = @import("std");
const mem = std.mem;
const crypto = std.crypto;

fn fieldElement(comptime Field: type) type {
    return struct {
        const Self = @This();

        limbs: Field.Limbs,

        pub const bytes = Field.bytes;

        pub fn invert(a: Self) Self {
            const iterations = (49 * Field.len_prime + if (Field.len_prime < 46) 80 else 57) / 17;
            const XLimbs = [a.limbs.len + 1]Field.Word;

            var d: Field.Word = 1;
            var f: XLimbs = undefined;
            Field.fiatP256Msat(&f);

            var g = mem.zeroes(XLimbs);
            Field.fiatP256FromMontgomery(g[0..a.limbs.len], a.limbs); // Assume input in Montgomery domain

            var r = one.limbs;
            var v = mem.zeroes(Field.Limbs);

            var precomp: Field.Limbs = undefined;
            Field.fiatP256DivstepPrecomp(&precomp);

            var out1: Field.Word = undefined;
            var out2: XLimbs = undefined;
            var out3: XLimbs = undefined;
            var out4: Field.Limbs = undefined;
            var out5: Field.Limbs = undefined;
            var i: usize = 0;
            while (i < iterations - iterations % 2) : (i += 2) {
                Field.fiatP256Divstep(&out1, &out2, &out3, &out4, &out5, d, f, g, v, r);
                Field.fiatP256Divstep(&d, &f, &g, &v, &r, out1, out2, out3, out4, out5);
            }
            if (iterations % 2 != 0) {
                Field.fiatP256Divstep(&out1, &out2, &out3, &out4, &out5, d, f, g, v, r);
                v = out4;
                f = out2;
            }
            var v_opp: Field.Limbs = undefined;
            Field.fiatP256Opp(&v_opp, v);
            Field.fiatP256Selectznz(&v, @truncate(u1, f[f.len - 1] >> (std.meta.bitCount(Field.Word) - 1)), v, v_opp);
            var fe: Self = undefined;
            Field.fiatP256Mul(&fe.limbs, v, precomp);
            return fe;
        }

        pub const one = comptime one: {
            var fe: Self = undefined;
            Field.fiatP256SetOne(&fe.limbs);
            break :one fe;
        };

        pub fn fromBytes(s: [Field.bytes]u8) Self {
            var limbs_z: Field.Limbs = undefined;
            Field.fiatP256FromBytes(&limbs_z, s);
            var limbs: Field.Limbs = undefined;
            Field.fiatP256ToMontgomery(&limbs, limbs_z);
            return Self{ .limbs = limbs };
        }

        pub fn mul(a: Self, b: Self) Self {
            var fe: Self = undefined;
            Field.fiatP256Mul(&fe.limbs, a.limbs, b.limbs);
            return fe;
        }

        pub fn eql(a: Self, b: Self) bool {
            return crypto.utils.timingSafeEql(Field.Limbs, a.limbs, b.limbs);
        }
    };
}

test "Field inversion" {
    const Fe = fieldElement(struct {
        pub usingnamespace @import("p256_64.zig");
        const Word = u64;
        const Limbs = [4]Word;
        pub const len_prime = 256;
        pub const bytes = 32;
    });

    var s: [Fe.bytes]u8 = undefined;
    crypto.random.bytes(&s);
    const x = Fe.fromBytes(s);

    const xinv = x.invert();
    std.testing.expect(x.mul(xinv).eql(Fe.one));
}
