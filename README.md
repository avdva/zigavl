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
pub fn deleteFirst(self: *Self) ?KV
pub fn deleteLast(self: *Self) ?KV
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

## Example

[Runnable usage example](src/lib.zig).

## Benchmarks

See the [benchmark guide](docs/benchmarks.md) for commands, workload definitions,
measurement recommendations, and limitations.

## Contact

[Aleksandr Demakin](mailto:alexander.demakin@gmail.com)

## License

Source code is available under the [Apache License Version 2.0](/LICENSE).
