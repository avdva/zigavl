const std = @import("std");
const lib = @import("lib.zig");

const Tree = lib.Tree;
const TreeWithOptions = lib.TreeWithOptions;
const Options = lib.Options;

fn i64Cmp(a: i64, b: i64) std.math.Order {
    return std.math.order(a, b);
}

test "empty tree" {
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(std.testing.allocator);
    defer t.deinit();

    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.iteratorAtFirst().value());
    try std.testing.expectEqual(@as(?i64, null), t.delete(0));
}

fn testTreeClear(comptime options: Options) !void {
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(std.testing.allocator);
    defer t.deinit();

    t.clear();
    try std.testing.expectEqual(@as(usize, 0), t.len());

    for (0..128) |idx| {
        const key: i64 = @intCast(idx);
        _ = try t.insert(key, key);
    }

    t.clear();
    try std.testing.expectEqual(@as(usize, 0), t.len());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMin());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMax());
    try std.testing.expectEqual(@as(?*i64, null), t.get(64));
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.iteratorAtFirst().value());
    try std.testing.expectEqual(@as(?usize, null), t.rank(64));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(0, 127));

    const inserted = try t.insert(42, 100);
    try std.testing.expect(inserted.inserted);
    try std.testing.expectEqual(@as(i64, 100), t.get(42).?.*);
}

test "tree clear across options" {
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .PointerBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .PointerBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .ArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .StableArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .SplitArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

fn testCompactStorage(comptime options: Options) !void {
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(std.testing.allocator);
    defer t.deinit();

    for (0..16) |idx| {
        const key: i64 = @intCast(idx);
        _ = try t.insert(key, key * 10);
    }
    for ([_]i64{ 1, 3, 6, 7 }) |key| {
        _ = t.delete(key);
    }

    t.compactStorage();

    const expected = [_]i64{ 0, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15 };
    try std.testing.expectEqual(expected.len, t.len());
    var it = t.iteratorAtFirst();
    for (expected) |key| {
        const entry = it.value() orelse return error.MissingEntry;
        try std.testing.expectEqual(key, entry.Key);
        try std.testing.expectEqual(key * 10, entry.Value.*);
        it.next();
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());
}

test "tree compactStorage across options" {
    try testCompactStorage(.{ .countChildren = true, .nodeCacheType = .PointerBased });
    try testCompactStorage(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testCompactStorage(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testCompactStorage(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

fn sortedRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return null,
            .eq => return idx,
            .gt => {},
        }
    }
    return null;
}

fn sortedLowerBoundRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt, .eq => return idx,
            .gt => {},
        }
    }
    return null;
}

fn sortedFloorRank(keys: []const i64, key: i64) ?usize {
    var result: ?usize = null;
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return result,
            .eq => return idx,
            .gt => result = idx,
        }
    }
    return result;
}

fn sortedUpperBoundRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return idx,
            .eq, .gt => {},
        }
    }
    return null;
}

fn sortedCountInRange(keys: []const i64, k1: i64, k2: i64) usize {
    const r1 = sortedLowerBoundRank(keys, k1) orelse return 0;
    const r2 = sortedFloorRank(keys, k2) orelse return 0;
    return if (r2 >= r1) r2 - r1 + 1 else 0;
}

fn sortedRankDistance(keys: []const i64, k1: i64, k2: i64) ?usize {
    const r1 = sortedRank(keys, k1) orelse return null;
    const r2 = sortedRank(keys, k2) orelse return null;
    return if (r2 >= r1) r2 - r1 else r1 - r2;
}

fn expectOptionalEntryKey(comptime Entry: type, expected: ?i64, actual: ?Entry) !void {
    if (expected) |key| {
        try std.testing.expect(actual != null);
        try std.testing.expectEqual(key, actual.?.Key);
    } else {
        try std.testing.expectEqual(@as(?Entry, null), actual);
    }
}

fn expectRankRangeAndBounds(t: anytype, sorted_keys: []const i64, query_keys: []const i64) !void {
    const TreeType = @TypeOf(t.*);
    for (sorted_keys, 0..) |key, idx| {
        try std.testing.expectEqual(@as(?usize, idx), t.rank(key));
        try std.testing.expectEqual(key, t.at(idx).Key);
        try std.testing.expectEqual(key, t.iteratorAt(idx).value().?.Key);
    }

    for (query_keys) |key| {
        const lower_rank = sortedLowerBoundRank(sorted_keys, key);
        const lower_key = if (lower_rank) |rank| sorted_keys[rank] else null;
        try expectOptionalEntryKey(TreeType.Entry, lower_key, t.lowerBound(key).value());

        const upper_rank = sortedUpperBoundRank(sorted_keys, key);
        const upper_key = if (upper_rank) |rank| sorted_keys[rank] else null;
        try expectOptionalEntryKey(TreeType.Entry, upper_key, t.upperBound(key).value());

        try std.testing.expectEqual(sortedRank(sorted_keys, key), t.rank(key));
    }

    for (query_keys) |k1| {
        for (query_keys) |k2| {
            try std.testing.expectEqual(sortedCountInRange(sorted_keys, k1, k2), t.countInRange(k1, k2));
            try std.testing.expectEqual(sortedRankDistance(sorted_keys, k1, k2), t.rankDistance(k1, k2));
        }
    }
}

fn testRankRangeAndBounds(comptime options: Options) !void {
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(std.testing.allocator);
    defer t.deinit();

    const sorted_keys = [_]i64{ -50, -10, 0, 3, 4, 10, 17, 31, 32, 99 };
    var insert_keys = sorted_keys;
    const query_keys = [_]i64{
        -60, -50, -49, -11, -10, -9, -1, 0,  1,  3,  4,   5,
        10,  16,  17,  18,  30,  31, 32, 33, 98, 99, 100,
    };

    var prng = std.Random.DefaultPrng.init(0x5eed);
    prng.random().shuffle(i64, &insert_keys);
    for (insert_keys) |key| {
        _ = try t.insert(key, key);
    }

    try expectRankRangeAndBounds(&t, &sorted_keys, &query_keys);
    t.orderStorageByKey();
    try expectRankRangeAndBounds(&t, &sorted_keys, &query_keys);
}

test "tree rank range and bounds match sorted slice across options" {
    try testRankRangeAndBounds(.{ .countChildren = false, .nodeCacheType = .PointerBased });
    try testRankRangeAndBounds(.{ .countChildren = true, .nodeCacheType = .PointerBased });
    try testRankRangeAndBounds(.{ .countChildren = false, .nodeCacheType = .ArrayBased });
    try testRankRangeAndBounds(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testRankRangeAndBounds(.{ .countChildren = false, .nodeCacheType = .StableArrayBased });
    try testRankRangeAndBounds(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testRankRangeAndBounds(.{ .countChildren = false, .nodeCacheType = .SplitArrayBased });
    try testRankRangeAndBounds(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

const Pair = struct {
    first: i64,
    second: i64,
};

fn pairCmp(a: Pair, b: Pair) std.math.Order {
    return switch (std.math.order(a.first, b.first)) {
        .eq => std.math.order(a.second, b.second),
        else => |order| order,
    };
}

test "tree buildFromSorted rejects unsorted input without clearing tree" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(42, 420);

    const duplicate_items = [_]TreeType.KV{
        .{ .Key = 1, .Value = 10 },
        .{ .Key = 1, .Value = 11 },
    };
    try std.testing.expectError(error.ItemsNotStrictlySorted, t.buildFromSorted(&duplicate_items));
    try std.testing.expectEqual(@as(usize, 1), t.len());
    try std.testing.expectEqual(@as(i64, 420), t.get(42).?.*);

    const unsorted_items = [_]TreeType.KV{
        .{ .Key = 2, .Value = 20 },
        .{ .Key = 1, .Value = 10 },
    };
    try std.testing.expectError(error.ItemsNotStrictlySorted, t.buildFromSorted(&unsorted_items));
    try std.testing.expectEqual(@as(usize, 1), t.len());
    try std.testing.expectEqual(@as(i64, 420), t.get(42).?.*);
}

test "tree buildFromSorted accepts empty input" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(42, 420);
    const empty_items = [_]TreeType.KV{};
    try t.buildFromSorted(&empty_items);

    try std.testing.expectEqual(@as(usize, 0), t.len());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMin());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMax());
}

test "tree orderStorageByKey is noop for pointer cache" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .nodeCacheType = .PointerBased });
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(2, 20);
    _ = try t.insert(1, 10);
    _ = try t.insert(3, 30);

    t.orderStorageByKey();

    try std.testing.expectEqual(@as(usize, 3), t.len());
    try std.testing.expectEqual(@as(i64, 1), t.at(0).Key);
    try std.testing.expectEqual(@as(i64, 2), t.at(1).Key);
    try std.testing.expectEqual(@as(i64, 3), t.at(2).Key);
}

test "tree getOrInsert" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();
    var ir = t.insert(1, 1) catch unreachable;
    try std.testing.expectEqual(true, ir.inserted);
    ir = try t.getOrInsert(1, 2);
    try std.testing.expectEqual(false, ir.inserted);
    try std.testing.expectEqual(@as(i64, 1), ir.v.*);
    ir = t.insert(1, 1) catch unreachable;
    try std.testing.expectEqual(false, ir.inserted);
    ir.v.* = 2;
    try std.testing.expectEqual(@as(i64, 2), t.get(1).?.*);
    ir = try t.getOrInsert(2, 2);
    try std.testing.expectEqual(@as(i64, 2), t.get(2).?.*);
    ir.v.* = 3;
    try std.testing.expectEqual(@as(i64, 3), t.get(2).?.*);
}

test "stable array based value pointers survive cache growth" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .nodeCacheType = .StableArrayBased });
    var t = try TreeType.init(a);
    defer t.deinit();

    const first = (try t.insert(0, 42)).v;
    for (1..4096) |idx| {
        const key: i64 = @intCast(idx);
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(i64, 42), first.*);
    first.* = 99;
    try std.testing.expectEqual(@as(i64, 99), t.get(0).?.*);
}

test "delete min" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i <= 128) {
        const e = t.getMin();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        try std.testing.expectEqual(i, t.delete(i).?);
        i += 1;
    }
    const exp_len: usize = 0;
    try std.testing.expectEqual(exp_len, t.len());
}

test "delete max" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i <= 128) {
        const e = t.getMax();
        try std.testing.expectEqual(128 - i, e.?.Key);
        try std.testing.expectEqual(128 - i, e.?.Value.*);
        try std.testing.expectEqual(128 - i, t.delete(128 - i).?);
        i += 1;
    }
    const exp_len: usize = 0;
    try std.testing.expectEqual(exp_len, t.len());
}

test "tree at_countChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    i = 0;
    while (i <= 128) {
        const e = t.at(@as(usize, @intCast(i)));
        try std.testing.expectEqual(i, e.Key);
        try std.testing.expectEqual(i, e.Value.*);
        i += 1;
    }
}

test "tree at_nocountChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = false });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    i = 0;
    while (i <= 128) {
        const e = t.at(@as(usize, @intCast(i)));
        try std.testing.expectEqual(i, e.Key);
        try std.testing.expectEqual(i, e.Value.*);
        i += 1;
    }
}

test "tree deleteAt" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    var exp_len: usize = 128;
    i = 64;
    while (i < 128) {
        try std.testing.expectEqual(exp_len, t.len());
        const kv = t.deleteAt(64);
        try std.testing.expectEqual(i, kv.Key);
        try std.testing.expectEqual(i, kv.Value);
        i += 1;
        exp_len -= 1;
    }

    i = 0;
    while (i < 64) {
        try std.testing.expectEqual(exp_len, t.len());
        const kv = t.deleteAt(0);
        try std.testing.expectEqual(i, kv.Key);
        try std.testing.expectEqual(i, kv.Value);
        i += 1;
        exp_len -= 1;
    }
    try std.testing.expectEqual(exp_len, t.len());
}

test "tree iterator" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    var it = t.iteratorAtFirst();
    i = 0;
    while (i < 128) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.next();
        i += 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.iteratorAtLast();
    i = 127;
    while (i >= 0) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.prev();
        i -= 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.iteratorAtFirst();
    i = 0;
    while (i < 64) {
        try std.testing.expect(it.value() != null);
        i += 1;
        it.next();
    }
    i = 0;
    while (i < 64) {
        const e = it.value();
        try std.testing.expectEqual(i + 64, e.?.Key);
        try std.testing.expectEqual(i + 64, e.?.Value.*);
        it = t.deleteIterator(it);
        i += 1;
    }

    it = t.iteratorAtFirst();
    i = 0;
    while (i < 64) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it = t.deleteIterator(it);
        i += 1;
    }

    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());
}

test "tree iteratorAt" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i < 128) {
        var it = t.iteratorAt(@as(usize, @intCast(i)));
        var e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        var j = i - 1;
        while (j >= 0) {
            it.prev();
            e = it.value();
            try std.testing.expectEqual(j, e.?.Key);
            try std.testing.expectEqual(j, e.?.Value.*);
            j -= 1;
        }
        it = t.iteratorAt(@as(usize, @intCast(i)));
        j = i + 1;
        while (j < t.len()) {
            it.next();
            e = it.value();
            try std.testing.expectEqual(j, e.?.Key);
            try std.testing.expectEqual(j, e.?.Value.*);
            j += 1;
        }
        i += 1;
    }
}

test "tree bounds" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    for ([_]i64{ 0, 10, 20, 30, 40 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(i64, 10), t.lowerBound(5).value().?.Key);
    try std.testing.expectEqual(@as(i64, 10), t.lowerBound(10).value().?.Key);
    try std.testing.expectEqual(@as(i64, 20), t.lowerBound(20).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.lowerBound(25).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.lowerBound(30).value().?.Key);
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.lowerBound(41).value());

    try std.testing.expectEqual(@as(i64, 10), t.upperBound(5).value().?.Key);
    try std.testing.expectEqual(@as(i64, 20), t.upperBound(10).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.upperBound(20).value().?.Key);
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.upperBound(40).value());
}

test "tree bounds with composite keys" {
    const a = std.testing.allocator;
    const TreeType = Tree(Pair, i64, pairCmp);
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(.{ .first = 10, .second = 10 }, 10);
    _ = try t.insert(.{ .first = 20, .second = 20 }, 20);
    _ = try t.insert(.{ .first = 20, .second = 30 }, 30);
    _ = try t.insert(.{ .first = 30, .second = 40 }, 40);

    try std.testing.expectEqual(Pair{ .first = 20, .second = 20 }, t.lowerBound(.{ .first = 20, .second = 0 }).value().?.Key);
    try std.testing.expectEqual(Pair{ .first = 20, .second = 20 }, t.lowerBound(.{ .first = 20, .second = 20 }).value().?.Key);
    try std.testing.expectEqual(Pair{ .first = 30, .second = 40 }, t.upperBound(.{ .first = 20, .second = 30 }).value().?.Key);
    try std.testing.expectEqual(@as(?usize, 1), t.rank(.{ .first = 20, .second = 20 }));
    try std.testing.expectEqual(@as(?usize, 2), t.rank(.{ .first = 20, .second = 30 }));
    try std.testing.expectEqual(@as(?usize, null), t.rank(.{ .first = 20, .second = 25 }));
}

test "test public declarations" {
    const a = std.testing.allocator;
    const TreeType = lib.TreeWithOptions(i64, i64, i64Cmp, lib.Options{
        .countChildren = false,
        .nodeCacheType = lib.NodeCacheType.ArrayBased,
    });
    const options = lib.InitOptions{
        .allowFastDeinit = .auto,
    };
    var aa = std.heap.ArenaAllocator.init(a);
    defer aa.deinit();
    var t = try TreeType.initWithOptions(aa.allocator(), options);
    defer t.deinit();
    _ = try t.insert(0, 0);
    var it = t.iteratorAtFirst();
    const min = t.getMin().?;
    try std.testing.expectEqual(it.value().?.Key, min.Key);
    const max = t.getMax().?;
    it = t.iteratorAtLast();
    try std.testing.expectEqual(it.value().?.Key, max.Key);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).Key);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).Value.*);
    try std.testing.expectEqual(@as(i64, 0), t.delete(0).?);
    try std.testing.expectEqual(@as(usize, 0), t.len());
    t.clear();
    try std.testing.expectEqual(@as(usize, 0), t.len());
}

test "tree example usage" {
    var gpa = std.heap.DebugAllocator(.{}){};
    defer _ = gpa.detectLeaks();
    // first, create an i64-->i64 tree
    const TreeType = lib.TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.initWithOptions(gpa.allocator(), .{ .allowFastDeinit = .auto });
    defer t.deinit();
    // add some elements
    var i: i64 = 10;
    while (i >= 0) {
        _ = try t.insert(i, i);
        i -= 1;
    }
    // get min and max
    if (t.getMin().?.Key != 0) {
        @panic("bad min");
    }
    if (t.getMax().?.Key != 10) {
        @panic("bad max");
    }
    // get an element by it's key
    if (t.get(5).?.* != 5) {
        @panic("invalid get result");
    }
    // iterate
    var it = t.iteratorAtFirst();
    i = 0;
    while (it.value()) |e| {
        if (e.Key != i) {
            @panic("invalid key");
        }
        if (e.Value.* != i) {
            @panic("invalid value");
        }
        i += 1;
        it.next();
    }
    //delete iterator
    var second_it = t.deleteIterator(t.iteratorAtFirst());
    if (second_it.value().?.Key != 1 or second_it.value().?.Value.* != 1) {
        @panic("invalid deleteIterator result");
    }
    // delete by key
    if (t.delete(1).? != 1) {
        @panic("invalid delete result");
    }
    // delete by position
    const kv = t.deleteAt(0);
    if (kv.Key != 2 or kv.Value != 2) {
        @panic("invalid deleteAt result");
    }

    // ascend from pos.
    it = t.iteratorAt(3);
    if (it.value()) |val| {
        if (val.Key != 6) {
            @panic("invalid key");
        }
    } else {
        @panic("invalid iterator");
    }

    const updated_key_value = t.updateKey(5, 15);
    if (updated_key_value.?.* != 5) {
        @panic("invalid value");
    }

    if (t.rank(15) != 7) {
        @panic("invalid rank");
    }

    if (t.rankDistance(3, 15) != 7) {
        @panic("invalid rank distance");
    }

    if (t.countInRange(4, 15) != 7) {
        @panic("invalid range count");
    }

    // bulk-build from strictly sorted items.
    const sorted_items = [_]TreeType.KV{
        .{ .Key = 20, .Value = 200 },
        .{ .Key = 21, .Value = 210 },
        .{ .Key = 22, .Value = 220 },
    };
    try t.buildFromSorted(&sorted_items);
    if (t.getMin().?.Key != 20 or t.getMax().?.Key != 22) {
        @panic("invalid buildFromSorted result");
    }

    t.clear();
    if (t.len() != 0) {
        @panic("invalid clear result");
    }
}
