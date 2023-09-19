const std = @import("std");
const math = std.math;
const Tree = @import("./avl.zig").Tree;

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

test "test pub decls" {
    var a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = TreeType.init(a);
    defer t.deinit();
    _ = try t.insert(0, 0);
    var it = t.ascendFromStart();
    var min = t.getMin().?;
    try std.testing.expectEqual(it.value().?.k, min.k);
    var max = t.getMax().?;
    it = t.descendFromEnd();
    try std.testing.expectEqual(it.value().?.k, max.k);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).k);
    try std.testing.expectEqual(@as(i64, 0), t.at(0).v.*);
    try std.testing.expectEqual(@as(i64, 0), t.delete(0).?);
    try std.testing.expectEqual(@as(usize, 0), t.len());
}
