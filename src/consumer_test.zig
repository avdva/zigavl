const std = @import("std");
const zigavl = @import("zigavl");

fn i64Cmp(a: i64, b: i64) std.math.Order {
    return std.math.order(a, b);
}

test "zigavl module can be imported by consumers" {
    const Tree = zigavl.Tree(i64, i64, i64Cmp);
    var tree = try Tree.init(std.testing.allocator);
    defer tree.deinit();

    _ = try tree.insert(2, 20);
    _ = try tree.insert(1, 10);

    try std.testing.expectEqual(@as(usize, 2), tree.len());
    try std.testing.expectEqual(@as(i64, 10), tree.get(1).?.*);
    try std.testing.expectEqual(@as(i64, 1), tree.iteratorAtFirst().value().?.Key);
    tree.clearRetainingCapacity();
    try std.testing.expectEqual(@as(usize, 0), tree.len());
    _ = try tree.insert(3, 30);
    _ = try tree.insert(7, 70);
    try std.testing.expectEqual(@as(i64, 3), tree.deleteFirst().?.Key);
    try std.testing.expectEqual(@as(i64, 70), tree.deleteLast().?.Value);
    try std.testing.expect(tree.deleteFirst() == null and tree.deleteLast() == null);
}
