const std = @import("std");
const fiat = @import("fiat");

fn functionCount() usize {
    var n: usize = 0;
    for (std.meta.declarations(fiat)) |name| {
        if (@typeInfo(@TypeOf(@field(fiat, name))) == .@"fn") n += 1;
    }
    return n;
}

export const fiat_functions = blk: {
    var fns: [functionCount()]*const anyopaque = undefined;
    var i: usize = 0;
    for (std.meta.declarations(fiat)) |name| {
        const decl = @field(fiat, name);
        if (@typeInfo(@TypeOf(decl)) == .@"fn") {
            fns[i] = @ptrCast(&decl);
            i += 1;
        }
    }
    const result = fns;
    break :blk result;
};
