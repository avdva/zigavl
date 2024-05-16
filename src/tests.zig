const std = @import("std");
const math = std.math;
const lib = @import("./lib.zig");

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

test "test pub decls" {
    const a = std.testing.allocator;
    const TreeType = lib.Tree(i64, i64, i64Cmp);
    var t = TreeType.init(a);
    defer t.deinit();
    _ = try t.insert(0, 0);
    var it = t.ascendFromStart();
    const min = t.getMin().?;
    try std.testing.expectEqual(it.value().?.k, min.k);
    const max = t.getMax().?;
    it = t.descendFromEnd();
    try std.testing.expectEqual(it.value().?.k, max.k);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).k);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).v.*);
    try std.testing.expectEqual(@as(i64, 0), t.delete(0).?);
    try std.testing.expectEqual(@as(usize, 0), t.len());
}

test "tree example usage" {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.detectLeaks();
    // first, create an i64-->i64 tree
    const TreeType = lib.TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = TreeType.init(gpa.allocator());
    defer t.deinit();
    // add some elements
    var i: i64 = 10;
    while (i >= 0) {
        _ = try t.insert(i, i);
        i -= 1;
    }
    // get min and max
    if (t.getMin().?.k != 0) {
        @panic("bad min");
    }
    if (t.getMax().?.k != 10) {
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
        if (e.k != i) {
            @panic("invalid key");
        }
        if (e.v.* != i) {
            @panic("invalid value");
        }
        i += 1;
        it.next();
    }
    //delete iterator
    var second_it = t.deleteIterator(t.ascendFromStart());
    if (second_it.value().?.k != 1 or second_it.value().?.v.* != 1) {
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
        if (val.k != 6) {
            @panic("invalid key");
        }
    } else {
        @panic("invalid iterator");
    }
}
