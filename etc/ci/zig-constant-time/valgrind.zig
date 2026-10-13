//! Calls every public function of the `fiat` module on random inputs that
//! are marked as secret with `std.crypto.timing_safe.classify`.  Run under
//! `valgrind --error-exitcode=1`, memcheck then reports every conditional
//! jump and every memory access whose address depends on an input.
//!
//! Build with `-fvalgrind`, otherwise `classify` does nothing.

const std = @import("std");
const fiat = @import("fiat");
const timing_safe = std.crypto.timing_safe;

/// Fills `x` (an integer or a possibly nested array of integers) with
/// random bits.
fn randomize(rng: std.Random, x: anytype) void {
    switch (@typeInfo(@TypeOf(x.*))) {
        .int => x.* = rng.int(@TypeOf(x.*)),
        .bool => x.* = rng.boolean(),
        .array => for (x) |*e| randomize(rng, e),
        else => @compileError("unsupported argument type " ++ @typeName(@TypeOf(x.*))),
    }
}

fn callOnSecretInputs(rng: std.Random, comptime f: anytype) void {
    const params = @typeInfo(@TypeOf(f)).@"fn".param_types;
    var args: std.meta.ArgsTuple(@TypeOf(f)) = undefined;
    // Storage for the outputs, which are passed as pointers.
    var outputs: [params.len][256]u8 align(64) = undefined;
    inline for (params, 0..) |T, i| {
        switch (@typeInfo(T.?)) {
            .pointer => |p| {
                comptime std.debug.assert(@sizeOf(p.child) <= outputs[i].len);
                args[i] = @ptrCast(@alignCast(&outputs[i]));
            },
            else => {
                randomize(rng, &args[i]);
                timing_safe.classify(&args[i]);
            },
        }
    }
    @call(.never_inline, f, args);
    // Only to keep the outputs alive; they are never inspected.
    std.mem.doNotOptimizeAway(&outputs);
}

pub fn main() void {
    var prng = std.Random.DefaultPrng.init(0x5eed);
    const rng = prng.random();
    inline for (comptime std.meta.declarations(fiat)) |name| {
        const decl = @field(fiat, name);
        if (@typeInfo(@TypeOf(decl)) == .@"fn") callOnSecretInputs(rng, decl);
    }
}
