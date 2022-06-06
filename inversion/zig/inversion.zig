const std = @import("std");
const mem = std.mem;
const crypto = std.crypto;

fn fieldElement(comptime Field: type) type {
    const fiat = Field.fiat;

    return struct {
        const Self = @This();

        limbs: Field.Limbs,

        pub const bytes = Field.bytes;

        pub fn invert(a: Self) Self {
            const iterations = (49 * Field.len_prime + if (Field.len_prime < 46) 80 else 57) / 17;
            const XLimbs = [a.limbs.len + 1]Field.Word;

            var d: Field.Word = 1;
            var f = comptime x: {
                var f: XLimbs = undefined;
                fiat.msat(&f);
                break :x f;
            };

            var g = mem.zeroes(XLimbs);
            fiat.fromMontgomery(g[0..a.limbs.len], a.limbs); // Assume input in Montgomery domain

            var r = one.limbs;
            var v = mem.zeroes(Field.Limbs);

            var out1: Field.Word = undefined;
            var out2: XLimbs = undefined;
            var out3: XLimbs = undefined;
            var out4: Field.Limbs = undefined;
            var out5: Field.Limbs = undefined;
            var i: usize = 0;
            while (i < iterations - iterations % 2) : (i += 2) {
                fiat.divstep(&out1, &out2, &out3, &out4, &out5, d, f, g, v, r);
                fiat.divstep(&d, &f, &g, &v, &r, out1, out2, out3, out4, out5);
            }
            if (iterations % 2 != 0) {
                fiat.divstep(&out1, &out2, &out3, &out4, &out5, d, f, g, v, r);
                v = out4;
                f = out2;
            }
            var v_opp: Field.Limbs = undefined;
            fiat.opp(&v_opp, v);
            fiat.selectznz(&v, @truncate(u1, f[f.len - 1] >> (std.meta.bitCount(Field.Word) - 1)), v, v_opp);

            const precomp = comptime x: {
                var precomp: Field.Limbs = undefined;
                fiat.divstepPrecomp(&precomp);
                break :x precomp;
            };
            var fe: Self = undefined;
            fiat.mul(&fe.limbs, v, precomp);
            return fe;
        }

        pub const one = one: {
            var fe: Self = undefined;
            fiat.setOne(&fe.limbs);
            break :one fe;
        };

        pub fn fromBytes(s: [Field.bytes]u8) Self {
            var limbs_z: Field.Limbs = undefined;
            fiat.fromBytes(&limbs_z, s);
            var limbs: Field.Limbs = undefined;
            fiat.toMontgomery(&limbs, limbs_z);
            return Self{ .limbs = limbs };
        }

        pub fn mul(a: Self, b: Self) Self {
            var fe: Self = undefined;
            fiat.mul(&fe.limbs, a.limbs, b.limbs);
            return fe;
        }

        pub fn eql(a: Self, b: Self) bool {
            return crypto.utils.timingSafeEql(Field.Limbs, a.limbs, b.limbs);
        }
    };
}

test "Field inversion" {
    const Fe = fieldElement(struct {
        const fiat = @import("p256_64.zig");
        const Word = u64;
        const Limbs = [4]Word;
        const len_prime = 256;
        const bytes = 32;
    });

    var s: [Fe.bytes]u8 = undefined;
    crypto.random.bytes(&s);
    const x = Fe.fromBytes(s);

    const xinv = x.invert();
    try std.testing.expect(x.mul(xinv).eql(Fe.one));
}
