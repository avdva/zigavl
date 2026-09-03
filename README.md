# zigavl
A self-balancing binary [AVL](https://en.wikipedia.org/wiki/AVL_tree) tree written in Zig.

# Presentation
To use this library, you need at least Zig 0.16.x.

## Badges

![Build Status](https://img.shields.io/github/actions/workflow/status/avdva/zigavl/workflow.yml?branch=main)

## Installation

Add zigavl to your `build.zig.zon`:

```sh
zig fetch --save git+https://github.com/avdva/zigavl#v1.2.0
```

Then expose the dependency module in your `build.zig`:

```zig
const zigavl = b.dependency("zigavl", .{
    .target = target,
    .optimize = optimize,
});
exe.root_module.addImport("zigavl", zigavl.module("zigavl"));
```

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
pub fn clear(self: *Self) void
pub fn compactStorage(self: *Self) void
pub fn orderStorageByKey(self: *Self) void

// insert:
pub fn buildFromSorted(self: *Self, items: []const KV) !void
pub fn insert(self: *Self, k: K, v: V) !InsertResult
pub fn getOrInsert(self: *Self, k: K, v: V) !InsertResult 
pub fn getOrEmplace(self: *Self, k: K, ctor: fn (v: *V, args: anytype) void, args: anytype) !InsertResult
pub fn updateKey(self: *Self, old_key: K, new_key: K) ?*V

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
pub fn rank(self: *Self, k: K) ?usize
pub fn rankDistance(self: *Self, k1: K, k2: K) ?usize
pub fn countInRange(self: *Self, k1: K, k2: K) usize
pub fn at(self: *Self, pos: usize) Entry
pub fn deleteAt(self: *Self, pos: usize) KV

// iterate:
pub fn iteratorAtFirst(self: *Self) Iterator
pub fn iteratorAtLast(self: *Self) Iterator
pub fn iteratorAt(self: *Self, pos: usize) Iterator
pub fn lowerBound(self: *Self, k: K) Iterator
pub fn upperBound(self: *Self, k: K) Iterator

```

Notes:
- `countChildren = true` enables `O(logn)` positional access. Without it, `rank`, `rankDistance`, `countInRange`, `at`, `iteratorAt`, and `deleteAt` may scan linearly. It stores child counts as `u32`, so trees larger than `maxInt(u32) + 1` elements are not supported in this mode.
- `nodeCacheType = .PointerBased` allocates nodes separately and keeps returned value pointers stable across future insertions.
- `nodeCacheType = .ArrayBased` stores tree nodes in an array-backed free-list cache instead of allocating each node separately. Future insertions may reallocate storage and invalidate previously returned value pointers.
- `nodeCacheType = .StableArrayBased` stores tree nodes in fixed-size chunks. It keeps returned value pointers stable across future insertions, while memory usage can grow to the peak node count until `compactStorage`, `clear`, or `deinit`.
- `nodeCacheType = .SplitArrayBased` stores keys, values, metadata, and tree links in separate contiguous arrays. It is experimental and can reduce cache traffic for lookup-heavy workloads; future insertions may reallocate storage and invalidate previously returned value pointers.
- `compactStorage()` compacts address-based caches after deletions. `.ArrayBased` and `.SplitArrayBased` can shrink backing arrays, `.StableArrayBased` can free unused tail chunks, and `.PointerBased` treats it as a no-op.
- `orderStorageByKey()` orders supported address-based cache storage by sorted key order. It is useful when a tree is built or bulk-mutated first and then queried many times by key or sorted position. After it succeeds, `get` uses binary search over dense storage in `O(logn)`, `at`, `iteratorAt`, and `deleteAt` resolve positions in `O(1)`, and iterator `next`/`prev` steps can advance through adjacent storage slots until the next structural mutation. The reordering itself is `O(n)`, and it may invalidate existing iterators, locations, entries, and value pointers. Currently this is supported by `.ArrayBased`, `.StableArrayBased`, and `.SplitArrayBased`.
- `buildFromSorted()` replaces the tree contents from strictly sorted unique `KV` items in `O(n)`. Invalid order or duplicate keys return `error.ItemsNotStrictlySorted` before the existing tree is cleared. Supported address-based caches are stored in key order immediately after the build.
- `clear()` removes all elements and releases node storage owned by the tree. Complexity depends on storage backend: `O(n)` for `.PointerBased`, `O(1)` for `.ArrayBased` and `.SplitArrayBased`, and `O(number_of_chunks)` for `.StableArrayBased`.
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

    // position iterator at a sorted position.
    it = t.iteratorAt(3);
    if (it.value()) |val| {
        if (val.Key != 6) {
            @panic("invalid key");
        }
    } else {
        @panic("invalid iterator");
    }

    // update key preserving old value.
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

```

Use `TreeWithOptions` to select a storage backend:

```zig
const LookupOptimizedTree = zigavl.TreeWithOptions(i64, i64, i64Cmp, .{
    .countChildren = true,
    .nodeCacheType = .SplitArrayBased,
});
```

## Benchmarks

Run the basic benchmark suite with:

```sh
zig build bench -Doptimize=ReleaseFast
```

The suite includes positional lookup benchmarks for the regular `O(logn)`
count-based path, the `O(1)` ordered-storage path, and the ordered-storage path
including the one-time `orderStorageByKey()` cost.

## Contact

[Aleksandr Demakin](mailto:alexander.demakin@gmail.com)

## License

Source code is available under the [Apache License Version 2.0](/LICENSE).
