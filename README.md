# zigavl
A self-balancing binary [AVL](https://en.wikipedia.org/wiki/AVL_tree) tree written in Zig.

# Presentation
To use this library, you need at least Zig 0.16.x.

## Badges

![Build Status](https://img.shields.io/github/actions/workflow/status/avdva/zigavl/workflow.yml?branch=main)

## API
```zig
// create tree type:
pub const Options = struct {
    countChildren: bool = false,
    nodeCacheType: NodeCacheType = .PointerBased,
};
pub fn TreeWithOptions(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order, comptime options: Options) type
pub fn Tree(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order) type

// init/deinit:
pub const InitOptions = struct {
    allowFastDeinit: enum { always, auto, never } = .never,
};
pub fn init(a: std.mem.Allocator) !Self
pub fn initWithOptions(a: std.mem.Allocator, io: InitOptions) !Self
pub fn deinit()

// insert:
pub fn insert(self: *Self, k: K, v: V) !InsertResult
pub fn getOrInsert(self: *Self, k: K, v: V) !InsertResult 
pub fn getOrEmplace(self: *Self, k: K, ctor: fn (v: *V, args: anytype) void, args: anytype) !InsertResult

// delete:
pub fn delete(self: *Self, k: K) ?V
pub fn deleteIterator(self: *Self, it: Iterator) Iterator

// find:
pub const Entry = struct {
    Key: K,
    Value: *V,
};
pub fn getMin(self: *Self) ?Entry
pub fn getMax(self: *Self) ?Entry
pub fn get(self: *Self, k: K) ?*V

// array-style access:
pub const KV = struct {
    Key: K,
    Value: V,
};
pub fn at(self: *Self, pos: usize) Entry
pub fn deleteAt(self: *Self, pos: usize) KV

// iterate:
pub fn ascendFromStart(self: *Self) Iterator
pub fn ascendAt(self: *Self, pos: usize) Iterator
pub fn descendFromEnd(self: *Self) Iterator

```

Notes:
- `countChildren = true` enables `O(logn)` positional access. It stores child counts as `u32`, so trees larger than `maxInt(u32) + 1` elements are not supported in this mode.
- `nodeCacheType = .ArrayBased` stores tree nodes in an array-backed free-list cache instead of allocating each node separately.
- `Entry.Value` points into the tree and can be used to update the stored value. `KV.Value` is an owned value copied out from a deleted node.
- Iterators are valid only for the tree that created them. If the node pointed to by an iterator is deleted, that iterator becomes invalid; use the iterator returned by `deleteIterator`.

Example:
```zig

const std = @import("std");
const math = std.math;
const zigavl = @import("zigavl");

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

pub fn main() !void {
    var gpa = std.heap.DebugAllocator(.{}){};
    defer _ = gpa.detectLeaks();
    // first, create an i64-->i64 tree
    const TreeType = zigavl.TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(gpa.allocator());
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

```

## Benchmarks

Run the basic benchmark suite with:

```sh
zig build bench -Doptimize=ReleaseFast
```

## Contact

[Aleksandr Demakin](mailto:alexander.demakin@gmail.com)

## License

Source code is available under the [Apache License Version 2.0](/LICENSE).
