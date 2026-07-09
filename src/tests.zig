const std = @import("std");
const math = std.math;
const lib = @import("lib.zig");

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

test "test pub decls" {
    const a = std.testing.allocator;
    const TreeType = lib.Tree(i64, i64, i64Cmp);
    const options = lib.InitOptions{
        .allowFastDeinit = .auto,
    };
    var aa = std.heap.ArenaAllocator.init(a);
    defer aa.deinit();
    var t = try TreeType.initWithOptions(aa.allocator(), options);
    defer t.deinit();
    _ = try t.insert(0, 0);
    var it = t.ascendFromStart();
    const min = t.getMin().?;
    try std.testing.expectEqual(it.value().?.Key, min.Key);
    const max = t.getMax().?;
    it = t.descendFromEnd();
    try std.testing.expectEqual(it.value().?.Key, max.Key);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).Key);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).Value.*);
    try std.testing.expectEqual(@as(i64, 0), t.delete(0).?);
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
    var it = t.ascendFromStart();
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
    var second_it = t.deleteIterator(t.ascendFromStart());
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
    it = t.ascendAt(3);
    if (it.value()) |val| {
        if (val.Key != 6) {
            @panic("invalid key");
        }
    } else {
        @panic("invalid iterator");
    }
}
