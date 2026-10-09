//! Functions that are not constant time, for `check.py --self-test`.

/// Compiles to a select of the two array pointers followed by loads.
pub fn selectArray(out1: *[4]u64, arg1: u1, arg2: [4]u64, arg3: [4]u64) void {
    out1.* = if (arg1 == 0) arg2 else arg3;
}

/// Loads from an address that depends on arg1.
pub fn tableLookup(out1: *u64, arg1: u1, arg2: [2]u64) void {
    out1.* = arg2[arg1];
}

/// Takes a number of iterations that depends on arg1.
pub fn collatzSteps(out1: *u64, arg1: u64) void {
    var x = arg1 | 1;
    var n: u64 = 0;
    while (x != 1) : (n += 1) {
        x = if (x & 1 == 0) x >> 1 else 3 * x + 1;
    }
    out1.* = n;
}
