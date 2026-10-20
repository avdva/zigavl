# zigavl
A self-balancing binary [AVL](https://en.wikipedia.org/wiki/AVL_tree) tree written in Zig.

# Presentation

Version `1.5.0` requires Zig 0.17.0 or newer. For Zig 0.16, use `v1.3.0`.

See the [1.5.0 release notes](docs/releases/1.5.0.md) for changes since 1.4.0.

## Badges

![Build Status](https://img.shields.io/github/actions/workflow/status/avdva/zigavl/workflow.yml?branch=main)

## Installation

Add `zigavl` to your `build.zig.zon`:

```sh
zig fetch --save git+https://github.com/avdva/zigavl#v1.5.0
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
pub fn TreeWithOptions(
    comptime K: type,
    comptime V: type,
    comptime Cmp: fn (a: K, b: K) math.Order,
    comptime options: Options,
) type
pub fn Tree(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order) type

// init/deinit:
pub const InitOptions = struct {
    allowFastDeinit: enum { always, auto, never } = .never,
};
pub fn init(a: std.mem.Allocator) !Self
pub fn initWithOptions(a: std.mem.Allocator, io: InitOptions) !Self
pub fn deinit()

// clear:
pub fn clear(self: *Self) void
pub fn clearRetainingCapacity(self: *Self) void

// insert/modify:
pub const InsertResult = struct {
    inserted: bool,
    v: *V,
};
pub fn buildFromSorted(self: *Self, items: []const KV) !void
pub fn insert(self: *Self, k: K, v: V) !InsertResult
pub fn getOrInsert(self: *Self, k: K, v: V) !InsertResult 
pub fn getOrEmplace(self: *Self, k: K, ctor: fn (v: *V, args: anytype) void, args: anytype) !InsertResult
pub fn updateKey(self: *Self, old_key: K, new_key: K) ?*V

// delete:
pub fn delete(self: *Self, k: K) ?V
pub fn popFirst(self: *Self) ?KV
pub fn popLast(self: *Self) ?KV
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

// storage-specific:
pub fn ensureCapacity(self: *Self, capacity: usize) !void // Address-based backends only.
pub fn compactStorage(self: *Self) void
pub fn orderStorageByKey(self: *Self) void

```

See [storage backends and selection guidance](docs/caches.md) for cache properties,
pointer stability, subtree counts, bulk loading, and storage maintenance.

Notes:
- `Entry.Value` points into the tree and can be used to update the stored value. `KV.Value` is an owned value.
- Iterators are valid only for the tree that created them. If the node pointed to by an iterator is deleted, that
  iterator becomes invalid; use the iterator returned by `deleteIterator`.

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

To reserve storage before inserting, select an address-based backend. For
example, inside a function using the imports and comparator above:

```zig
const ReservedTree = zigavl.TreeWithOptions(i64, i64, i64Cmp, .{
    .nodeCacheType = .ArrayBased,
});
var reserved = try ReservedTree.init(std.heap.page_allocator);
defer reserved.deinit();

try reserved.ensureCapacity(1_000);
_ = try reserved.insert(42, 420);

// Reuse the reservation for the next batch.
reserved.clearRetainingCapacity();
_ = try reserved.insert(7, 70);
_ = try reserved.insert(9, 90);

// Remove an edge directly, without searching by key.
const first = reserved.popFirst().?; // KV{ .Key = 7, .Value = 70 }
std.debug.assert(first.Key == 7 and first.Value == 70);
const last = reserved.popLast().?; // KV{ .Key = 9, .Value = 90 }
std.debug.assert(last.Key == 9 and last.Value == 90);
std.debug.assert(reserved.popLast() == null); // Empty tree.
```

`1_000` is the total live element capacity, including existing elements and
reusable free slots. Smaller requests do not shrink storage. PointerBased does
not support this method; see [capacity guarantees](docs/caches.md#reserving-capacity)
for pointer lifetimes and operations that can discard the reservation.
`clearRetainingCapacity()` empties array/chunk storage while keeping its capacity
for reuse; on PointerBased it frees nodes like `clear()`.

## Benchmarks

See the [benchmark guide](docs/benchmarks.md) for commands, workload definitions,
measurement recommendations, and limitations.

## Contact

[Aleksandr Demakin](mailto:alexander.demakin@gmail.com)

## License

Source code is available under the [Apache License Version 2.0](/LICENSE).
