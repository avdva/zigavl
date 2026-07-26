const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const zigavl_mod = b.addModule("zigavl", .{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib = b.addLibrary(.{
        .name = "zigavl",
        .linkage = .static,
        .root_module = zigavl_mod,
    });

    b.installArtifact(lib);

    const test_step = b.step("test", "Run unit tests");
    const unit_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/tests.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_unit_tests = b.addRunArtifact(unit_tests);
    test_step.dependOn(&run_unit_tests.step);

    const consumer_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/consumer_test.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    consumer_tests.root_module.addImport("zigavl", zigavl_mod);
    const run_consumer_tests = b.addRunArtifact(consumer_tests);
    test_step.dependOn(&run_consumer_tests.step);

    const bench_step = b.step("bench", "Run basic benchmarks");
    const bench = b.addExecutable(.{
        .name = "zigavl-bench",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/bench.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_bench = b.addRunArtifact(bench);
    bench_step.dependOn(&run_bench.step);
}
