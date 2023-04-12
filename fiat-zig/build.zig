const std = @import("std");

pub fn build(b: *std.Build) void {
    var main_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/main.zig" },
    });
    const run_main_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_main_tests.step);
}
