const std = @import("std");
const zigavl = @import("lib.zig");

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

fn shouldRun(filter: ?[]const u8, name: []const u8) bool {
    return filter == null or std.mem.indexOf(u8, name, filter.?) != null;
}

const CliArgs = struct {
    filter: ?[]const u8 = null,
    repeat: usize = 1,
};

fn parseArgs(args: []const [:0]const u8) !CliArgs {
    var parsed: CliArgs = .{};

    var idx: usize = 1;
    while (idx < args.len) : (idx += 1) {
        const arg = args[idx];
        if (std.mem.eql(u8, arg, "--repeat")) {
            idx += 1;
            if (idx == args.len) return error.MissingRepeatValue;
            parsed.repeat = try std.fmt.parseInt(usize, args[idx], 10);
        } else if (std.mem.startsWith(u8, arg, "--repeat=")) {
            parsed.repeat = try std.fmt.parseInt(usize, arg["--repeat=".len..], 10);
        } else if (std.mem.startsWith(u8, arg, "-")) {
            return error.UnknownArgument;
        } else {
            if (parsed.filter != null) return error.TooManyFilters;
            parsed.filter = arg;
        }
    }

    if (parsed.repeat == 0) return error.InvalidRepeat;
    return parsed;
}

fn report(name: []const u8, ops: usize, elapsed_ns: u64, checksum: i64) void {
    const ns_per_op = if (ops == 0) 0 else elapsed_ns / ops;
    const ps_per_op = if (ops == 0) 0 else elapsed_ns * 1000 / ops;
    std.debug.print("{s}: {d} ops, {d} ns/op, {d} ps/op, checksum={d}\n", .{
        name,
        ops,
        ns_per_op,
        ps_per_op,
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
    const bench_name = name ++ "/insert/sequential";
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
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchRandomInsert(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/insert/random";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        const result = try tree.insert(key, key);
        checksum += result.v.*;
    }
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn benchRandomGet(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/get/random";
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
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn benchRandomDelete(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/delete/random";
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
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn benchRandomUpdateKey(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/updateKey/random";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    const offset: i64 = @intCast(bench_len);
    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        checksum += tree.updateKey(key, key + offset).?.*;
    }
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn benchRandomDeleteInsert(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/delete-insert/random";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    const offset: i64 = @intCast(bench_len);
    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        const value = tree.delete(key).?;
        checksum += (try tree.insert(key + offset, value)).v.*;
    }
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn fillMixedUpdateKeyTree(comptime Tree: type, tree: *Tree, group_count: usize) !void {
    for (0..group_count) |group| {
        const base: i64 = @intCast(group * 8);
        _ = try tree.insert(base, base);
        _ = try tree.insert(base + 2, base + 2);
        _ = try tree.insert(base + 4, base + 4);
        _ = try tree.insert(base + 6, base + 6);
    }
}

fn mixedUpdateKeys(group_count: usize, op_id: usize) struct { old_key: i64, new_key: i64 } {
    const group = op_id / 3;
    const kind = op_id % 3;
    const base: i64 = @intCast(group * 8);
    const far_base: i64 = @intCast(group_count * 8 + 1024);
    return switch (kind) {
        0 => .{ .old_key = base + 2, .new_key = base + 3 }, // in-place
        1 => .{ .old_key = base, .new_key = base + 4 }, // overwrite existing
        else => .{ .old_key = base + 6, .new_key = far_base + @as(i64, @intCast(group)) }, // generic
    };
}

fn benchMixedUpdateKey(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/updateKey/mixed";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    const group_count = bench_len / 4;
    const op_count = group_count * 3;
    try fillMixedUpdateKeyTree(Tree, &tree, group_count);

    const op_ids = try makeKeys(a, op_count, true);
    defer a.free(op_ids);

    var checksum: i64 = 0;
    const start = nowNs();
    for (op_ids) |op_id| {
        const keys = mixedUpdateKeys(group_count, @intCast(op_id));
        checksum += tree.updateKey(keys.old_key, keys.new_key).?.*;
    }
    report(bench_name, op_count, nowNs() - start, checksum);
}

fn benchMixedDeleteInsert(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/delete-insert/mixed";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    const group_count = bench_len / 4;
    const op_count = group_count * 3;
    try fillMixedUpdateKeyTree(Tree, &tree, group_count);

    const op_ids = try makeKeys(a, op_count, true);
    defer a.free(op_ids);

    var checksum: i64 = 0;
    const start = nowNs();
    for (op_ids) |op_id| {
        const keys = mixedUpdateKeys(group_count, @intCast(op_id));
        const value = tree.delete(keys.old_key).?;
        checksum += (try tree.insert(keys.new_key, value)).v.*;
    }
    report(bench_name, op_count, nowNs() - start, checksum);
}

fn benchIterator(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/iterate/ascending";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    var it = tree.iteratorAtFirst();
    while (it.value()) |entry| {
        checksum += entry.Value.*;
        it.next();
    }
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchIteratorOrdered(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/iterate/ordered-ascending";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }
    tree.orderStorageByKey();

    var checksum: i64 = 0;
    const start = nowNs();
    var it = tree.iteratorAtFirst();
    while (it.value()) |entry| {
        checksum += entry.Value.*;
        it.next();
    }
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchAtCountChildren(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/at/logarithmic";
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
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchAtOrdered(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/at/ordered";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }
    tree.orderStorageByKey();

    var checksum: i64 = 0;
    const start = nowNs();
    for (0..bench_len) |idx| {
        checksum += tree.at(idx).Value.*;
    }
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchAtOrderedIncludingOrder(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator) !void {
    const bench_name = name ++ "/at/ordered-including-order";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }

    var checksum: i64 = 0;
    const start = nowNs();
    tree.orderStorageByKey();
    for (0..bench_len) |idx| {
        checksum += tree.at(idx).Value.*;
    }
    report(bench_name, bench_len, nowNs() - start, checksum);
}

fn benchGetOrderedStorage(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, keys: []const i64) !void {
    const bench_name = name ++ "/get/ordered-storage";
    const Tree = zigavl.TreeWithOptions(i64, i64, i64Cmp, options);
    var tree = try Tree.init(a);
    defer tree.deinit();

    for (0..bench_len) |idx| {
        const key: i64 = @intCast(idx);
        _ = try tree.insert(key, key);
    }
    tree.orderStorageByKey();

    var checksum: i64 = 0;
    const start = nowNs();
    for (keys) |key| {
        checksum += tree.get(key).?.*;
    }
    report(bench_name, keys.len, nowNs() - start, checksum);
}

fn benchTree(comptime name: []const u8, comptime options: zigavl.Options, a: std.mem.Allocator, random_keys: []const i64, filter: ?[]const u8) !void {
    if (shouldRun(filter, name ++ "/insert/sequential")) try benchSequentialInsert(name, options, a);
    if (shouldRun(filter, name ++ "/insert/random")) try benchRandomInsert(name, options, a, random_keys);
    if (shouldRun(filter, name ++ "/get/random")) try benchRandomGet(name, options, a, random_keys);
    if (shouldRun(filter, name ++ "/delete/random")) try benchRandomDelete(name, options, a, random_keys);
    if (shouldRun(filter, name ++ "/updateKey/random")) try benchRandomUpdateKey(name, options, a, random_keys);
    if (shouldRun(filter, name ++ "/delete-insert/random")) try benchRandomDeleteInsert(name, options, a, random_keys);
    if (shouldRun(filter, name ++ "/updateKey/mixed")) try benchMixedUpdateKey(name, options, a);
    if (shouldRun(filter, name ++ "/delete-insert/mixed")) try benchMixedDeleteInsert(name, options, a);
    if (shouldRun(filter, name ++ "/iterate/ascending")) try benchIterator(name, options, a);
    if (shouldRun(filter, name ++ "/at/logarithmic")) try benchAtCountChildren(name, .{
        .countChildren = true,
        .nodeCacheType = options.nodeCacheType,
    }, a);
    if (options.nodeCacheType == .ArrayBased or
        options.nodeCacheType == .StableArrayBased or
        options.nodeCacheType == .SplitArrayBased)
    {
        if (shouldRun(filter, name ++ "/iterate/ordered-ascending")) try benchIteratorOrdered(name, options, a);
        if (shouldRun(filter, name ++ "/at/ordered")) try benchAtOrdered(name, options, a);
        if (shouldRun(filter, name ++ "/at/ordered-including-order")) try benchAtOrderedIncludingOrder(name, options, a);
        if (shouldRun(filter, name ++ "/get/ordered-storage")) try benchGetOrderedStorage(name, options, a, random_keys);
    }
}

pub fn main(init: std.process.Init) !void {
    const a = std.heap.smp_allocator;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    const parsed = try parseArgs(args);

    const random_keys = try makeKeys(a, bench_len, true);
    defer a.free(random_keys);

    if (parsed.filter) |pattern| {
        std.debug.print("zigavl basic benchmarks: {d} items, filter={s}, repeat={d}\n", .{ bench_len, pattern, parsed.repeat });
    } else {
        std.debug.print("zigavl basic benchmarks: {d} items, repeat={d}\n", .{ bench_len, parsed.repeat });
    }

    for (0..parsed.repeat) |_| {
        try benchTree("pointer", .{ .nodeCacheType = .PointerBased }, a, random_keys, parsed.filter);
        try benchTree("array", .{ .nodeCacheType = .ArrayBased }, a, random_keys, parsed.filter);
        try benchTree("stable-array", .{ .nodeCacheType = .StableArrayBased }, a, random_keys, parsed.filter);
        try benchTree("split-array", .{ .nodeCacheType = .SplitArrayBased }, a, random_keys, parsed.filter);
    }
}
