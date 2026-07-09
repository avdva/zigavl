const std = @import("std");
const zigavl = @import("./lib.zig");

const bench_len = 250_000;
const posix = std.posix;

fn i64Cmp(a: i64, b: i64) std.math.Order {
    return std.math.order(a, b);
}

fn makeKeys(a: std.mem.Allocator, n: usize, shuffle: bool) ![]i64 {
    const keys = try a.alloc(i64, n);
    for (keys, 0..) |*key, idx| {
        key.* = @intCast(idx);
    }
    if (shuffle) {
        var prng = std.Random.DefaultPrng.init(0);
        prng.random().shuffle(i64, keys);
    }
    return keys;
}

fn report(name: []const u8, ops: usize, elapsed_ns: u64, checksum: i64) void {
    const ns_per_op = if (ops == 0) 0 else elapsed_ns / ops;
    std.debug.print("{s}: {d} ops, {d} ns/op, checksum={d}\n", .{
        name,
        ops,
        ns_per_op,
        checksum,
    });
}

fn nowNs() u64 {
    var ts: posix.timespec = undefined;
    const clock = switch (@import("builtin").os.tag) {
        .driverkit, .ios, .maccatalyst, .macos, .tvos, .visionos, .watchos => posix.CLOCK.UPTIME_RAW,
        else => posix.CLOCK.MONOTONIC,
    };
    switch (posix.errno(posix.system.clock_gettime(clock, &ts))) {
        .SUCCESS => return @intCast(@as(i128, ts.sec) * std.time.ns_per_s + ts.nsec),
        else => @panic("clock_gettime failed"),
    }
}

fn benchSequentialInsert(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    var checksum: i64 = 0;
    const start = nowNs();
    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        const result = try tree.insert(key, key);
        checksum += result.v.*;
    }
    report(name ++ "/insert/sequential", bench_len, nowNs() - start, checksum);
}

fn benchRandomInsert(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        const result = try tree.insert(key, key);
        checksum += result.v.*;
    }
    report(name ++ "/insert/random", keys.len, nowNs() - start, checksum);
}

fn benchRandomGet(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        checksum += tree.get(key).?.*;
    }
    report(name ++ "/get/random", keys.len, nowNs() - start, checksum);
}

fn benchRandomDelete(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        checksum += tree.delete(key).?;
    }
    report(name ++ "/delete/random", keys.len, nowNs() - start, checksum);
}

fn benchIterator(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    var it = tree.ascendFromStart();
    while (it.value()) |entry| {
        checksum += entry.Value.*;
        it.next();
    }
    report(name ++ "/iterate/ascending", bench_len, nowNs() - start, checksum);
}

fn benchAtCountChildren(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    for (0..bench_len) |idx| {
        checksum += tree.at(idx).Value.*;
    }
    report(name ++ "/at/countChildren", bench_len, nowNs() - start, checksum);
}

fn benchTree(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, random_keys: []const i64) !void {
    try benchSequentialInsert(name, options, a);
    try benchRandomInsert(name, options, a, random_keys);
    try benchRandomGet(name, options, a, random_keys);
    try benchRandomDelete(name, options, a, random_keys);
    try benchIterator(name, options, a);
    try benchAtCountChildren(name, .{
        .countChildren = true,
        .nodeCacheType = options.nodeCacheType,
    }, a);
}

pub fn main() !void {
    const a = std.heap.smp_allocator;
    const random_keys = try makeKeys(a, bench_len, true);
    defer a.free(random_keys);

    std.debug.print("zigavl basic benchmarks: {d} items\n", .{bench_len});
    try benchTree("pointer", .{ .nodeCacheType = .PointerBased }, a, random_keys);
    try benchTree("list", .{ .nodeCacheType = .ListBased }, a, random_keys);
    try benchTree("array", .{ .nodeCacheType = .ArrayBased }, a, random_keys);
}
