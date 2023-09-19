# zigavl
A self-balancing binary [AVL](https://en.wikipedia.org/wiki/AVL_tree) tree written in Zig.

## Badges

![Build Status](https://img.shields.io/github/actions/workflow/status/ultd/base58-zig/test.yml?branch=main)

## API
```
Create Generic tree type:
// Options defines some parameters of the tree.
pub const Options = struct {
    // countChildren, if set, enables children counts for every node of the tree.
    // the number of children allows to locate a node by its position with a guaranteed complexity O(logn).
    countChildren: bool = false,
};
pub fn TreeWithOptions(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order, comptime options: Options) type
pub fn Tree(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order) type

init/deinit:
pub fn init(a: std.mem.Allocator) Self
pub fn deinit()

insert:
pub fn getOrInsert(self: *Self, k: K, v: V) !InsertResult 
pub fn insert(self: *Self, k: K, v: V) !InsertResult

delete:
pub fn delete(self: *Self, k: K) ?V

find:
pub fn getMin(self: *Self) ?Entry
pub fn getMax(self: *Self) ?Entry
pub fn get(self: *Self, k: K) ?*V

array-style access:
pub fn at(self: *Self, pos: usize) Entry
pub fn deleteAt(self: *Self, pos: usize) V

iterate:
pub fn ascendFromStart(self: *Self) Iterator
pub fn descendFromEnd(self: *Self) Iterator

```

Example:
```
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.detectLeaks();
    const TreeType = lib.TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = TreeType.init(gpa.allocator());
    defer t.deinit();
    var i: i64 = 10;
    while (i >= 0) {
        _ = try t.insert(i, i);
        i -= 1;
    }
    if (t.getMin().?.k != 0) {
        @panic("bad min");
    }
    if (t.getMax().?.k != 10) {
        @panic("bad max");
    }
    if (t.get(5).?.* != 5) {
        @panic("invalid get result");
    }
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
}

```

## Contact

[Aleksandr Demakin](mailto:alexander.demakin@gmail.com)

## License

Source code is available under the [Apache License Version 2.0](/LICENSE).