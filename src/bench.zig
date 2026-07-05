const std = @import("std");
const zigavl = @import("./lib.zig");

const bench_len = 50_000;
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

fn benchSequentialInsert(a: std.mem.Allocator) !void {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = Tree.init(a);
    defer tree.deinit();

    var checksum: i64 = 0;
    const start = nowNs();
    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        const result = try tree.insert(key, key);
        checksum += result.v.*;
    }
    report("insert/sequential", bench_len, nowNs() - start, checksum);
}

fn benchRandomInsert(a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = Tree.init(a);
    defer tree.deinit();

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        const result = try tree.insert(key, key);
        checksum += result.v.*;
    }
    report("insert/random", keys.len, nowNs() - start, checksum);
}

fn benchRandomGet(a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = Tree.init(a);
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
    report("get/random", keys.len, nowNs() - start, checksum);
}

fn benchRandomDelete(a: std.mem.Allocator, keys: []const i64) !void {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = Tree.init(a);
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
    report("delete/random", keys.len, nowNs() - start, checksum);
}

fn benchIterator(a: std.mem.Allocator) !void {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = Tree.init(a);
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
    report("iterate/ascending", bench_len, nowNs() - start, checksum);
}

fn benchAtCountChildren(a: std.mem.Allocator) !void {
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var tree = Tree.init(a);
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
    report("at/countChildren", bench_len, nowNs() - start, checksum);
}

pub fn main() !void {
    const a = std.heap.smp_allocator;
    const random_keys = try makeKeys(a, bench_len, true);
    defer a.free(random_keys);

    std.debug.print("zigavl basic benchmarks: {d} items\n", .{bench_len});
    try benchSequentialInsert(a);
    try benchRandomInsert(a, random_keys);
    try benchRandomGet(a, random_keys);
    try benchRandomDelete(a, random_keys);
    try benchIterator(a);
    try benchAtCountChildren(a);
}
