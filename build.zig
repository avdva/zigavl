const std = @import("std");

pub fn build(b: *std.Build) void {
    const package_name = "zigavl";
    const package_path = "src/lib.zig";
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib = b.addStaticLibrary(.{
        .name = package_name,
        .root_source_file = .{ .src_path = .{ .owner = b, .sub_path = package_path } },
        .target = target,
        .optimize = optimize,
    });

    _ = b.addModule(package_name, .{
        .root_source_file = .{ .src_path = .{ .owner = b, .sub_path = package_path } },
    });

    b.installArtifact(lib);

    const main_tests = b.addTest(.{
        .root_source_file = .{ .src_path = .{ .owner = b, .sub_path = "src/tests.zig" } },
        .target = target,
        .optimize = optimize,
    });

    const run_main_tests = b.addRunArtifact(main_tests);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_main_tests.step);
}
