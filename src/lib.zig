const avl = @import("avl.zig");
pub const Tree = avl.Tree;
pub const TreeWithOptions = avl.TreeWithOptions;
pub const Options = avl.Options;
pub const InitOptions = avl.InitOptions;
pub const NodeCacheType = avl.NodeCacheType;

test "tree example usage" {
    const std = @import("std");
    const i64Cmp = struct {
        fn compare(a: i64, b: i64) std.math.Order {
            return std.math.order(a, b);
        }
    }.compare;
    // first, create an i64-->i64 tree
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.initWithOptions(std.testing.allocator, .{ .allowFastDeinit = .auto });
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
    // Get-or-insert preserves existing values; emplace constructs new ones.
    const existing = try t.getOrInsert(5, 500);
    try std.testing.expect(!existing.inserted);
    try std.testing.expectEqual(@as(i64, 5), existing.v.*);
    const added = try t.getOrInsert(11, 110);
    try std.testing.expect(added.inserted);
    try std.testing.expectEqual(@as(i64, 110), t.delete(11).?);
    const initialize = struct {
        fn value(ptr: *i64, initial: anytype) void {
            ptr.* = initial;
        }
    }.value;
    const emplaced = try t.getOrEmplace(12, initialize, @as(i64, 120));
    try std.testing.expect(emplaced.inserted);
    const retained = try t.getOrEmplace(12, initialize, @as(i64, 999));
    try std.testing.expect(!retained.inserted);
    try std.testing.expectEqual(@as(i64, 120), retained.v.*);
    try std.testing.expectEqual(@as(i64, 120), t.delete(12).?);

    // Bounds and positional access use the configured comparator.
    try std.testing.expectEqual(@as(i64, 4), t.lowerBound(4).value().?.Key);
    try std.testing.expectEqual(@as(i64, 5), t.upperBound(4).value().?.Key);
    try std.testing.expect(t.upperBound(10).value() == null);
    try std.testing.expectEqual(@as(i64, 4), t.at(4).Key);

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
    // Iterate in reverse using the same iterator type.
    it = t.iteratorAtLast();
    i = 10;
    while (it.value()) |entry| {
        try std.testing.expectEqual(i, entry.Key);
        try std.testing.expectEqual(i, entry.Value.*);
        i -= 1;
        it.prev();
    }
    try std.testing.expectEqual(@as(i64, -1), i);

    // delete iterator
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

    // position the iterator at a sorted position.
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

    // Remove owned pairs directly from each edge.
    const first = t.popFirst().?;
    try std.testing.expectEqual(TreeType.KV{ .Key = 20, .Value = 200 }, first);
    const last = t.popLast().?;
    try std.testing.expectEqual(TreeType.KV{ .Key = 22, .Value = 220 }, last);
    try std.testing.expectEqual(@as(usize, 1), t.len());

    t.clear();
    if (t.len() != 0) {
        @panic("invalid clear result");
    }

    try std.testing.expect(t.popFirst() == null and t.popLast() == null);

    // Reserve and reuse array storage between batches.
    const ReservedTree = TreeWithOptions(i64, i64, i64Cmp, .{ .nodeCacheType = .ArrayBased });
    var reserved = try ReservedTree.init(std.testing.allocator);
    defer reserved.deinit();
    try reserved.ensureCapacity(1_000);
    _ = try reserved.insert(42, 420);
    reserved.clearRetainingCapacity();
    try std.testing.expectEqual(@as(usize, 0), reserved.len());
    _ = try reserved.insert(7, 70);
    _ = try reserved.insert(9, 90);
    _ = try reserved.insert(8, 80);
    try std.testing.expectEqual(@as(i64, 80), reserved.delete(8).?);

    // Storage maintenance can discard the reservation and invalidate pointers.
    reserved.compactStorage();
    reserved.orderStorageByKey();
    try std.testing.expectEqual(@as(i64, 7), reserved.at(0).Key);
    try std.testing.expectEqual(@as(i64, 9), reserved.at(1).Key);
    try std.testing.expectEqual(ReservedTree.KV{ .Key = 7, .Value = 70 }, reserved.popFirst().?);
    try std.testing.expectEqual(ReservedTree.KV{ .Key = 9, .Value = 90 }, reserved.popLast().?);
    try std.testing.expect(reserved.popFirst() == null and reserved.popLast() == null);
}
