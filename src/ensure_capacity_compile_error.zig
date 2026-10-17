const std = @import("std");
const zigavl = @import("zigavl");

fn compare(a: i64, b: i64) std.math.Order {
    return std.math.order(a, b);
}

test "PointerBased rejects ensureCapacity at compile time" {
    var tree = try zigavl.Tree(i64, i64, compare).init(std.testing.allocator);
    defer tree.deinit();
    try tree.ensureCapacity(100);
}
