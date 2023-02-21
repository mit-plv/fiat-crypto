const std = @import("std");

pub fn build(b: *std.Build) void {
    var main_tests = b.addTest(.{
        .root_source_file = .{ .path = "inversion.zig" },
    });

    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&main_tests.step);
}
