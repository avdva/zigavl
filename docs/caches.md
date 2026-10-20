# Storage backends and selection guidance

[README](../README.md) · [Benchmark guide](benchmarks.md)

`nodeCacheType` selects how the tree owns and stores nodes. These caches are
storage backends, not caches that evict tree entries. Select the backend at
compile time with `TreeWithOptions`; `Tree` defaults to `PointerBased`.

## Choosing a backend

| Backend | Storage | Value pointers across insertions | Good starting point when |
|---|---|---|---|
| `PointerBased` | A separate allocation per node | Stable | You want the conservative default, keep value pointers, or need per-node allocation/release |
| `ArrayBased` | One growable array of nodes with a free list | May be invalidated by growth | You want contiguous storage and compact links, and can reacquire pointers after insertion |
| `StableArrayBased` | Fixed-size chunks of nodes with a free list | Stable | You need insertion-stable pointers while retaining compact links and chunk allocation |
| `SplitArrayBased` | Separate growable arrays of keys, values, metadata, and links | May be invalidated by growth | Searches dominate and values are large or rarely read in full; benchmark this experimental backend |

Pointer stability in this table applies to future insertions. Deleting a node,
clearing or rebuilding a tree invalidates references to removed nodes.
Compaction and ordering can move surviving nodes in address-based backends,
including StableArrayBased. Do not retain their old pointers or iterators across
those operations.

### PointerBased

Each node is allocated and freed through the supplied allocator. Tree links are
pointers, and existing value pointers survive further insertions. Individual
allocation can cost more than array/chunk growth; physical locality depends on
the allocator. Freed memory is returned to the allocator, which may retain it.

Choose this default when pointer lifetime is more important than layout tuning,
or when the allocator already matches your node lifetime well.

### ArrayBased

Nodes occupy a contiguous slot array. Links are 32-bit addresses; freed slots
are reused through a free list. This avoids allocating each node separately.
Growth may copy the backing array, invalidating previously returned `*V`
pointers even though logical node locations survive the reallocation.

Choose it when you can keep keys and reacquire values after insertion. It is a
useful baseline for locality-sensitive workloads, but not a guaranteed fastest
choice. Deletion retains slots/capacity for later reuse.

### StableArrayBased

Nodes are stored in separately allocated chunks of 1,024 slots, addressed by
compact 32-bit handles. Growing the chunk list does not move existing chunks,
so value pointers survive insertions. Address resolution adds a chunk lookup;
partially filled chunks and the chunk table also consume memory.

Choose it when insertion-stable pointers are required and chunk allocation is
preferable to allocating every node. Deletion retains slots for reuse; storage
can track the peak node count until compaction, clear, or deinit. Compaction
can free unused tail chunks but can also move live nodes.

### SplitArrayBased

Keys, values, metadata, and links are stored in separate contiguous arrays.
Searching can avoid touching large values until a match is found, potentially
reducing unrelated memory traffic. Mutations and growth maintain several
arrays, and growth may invalidate value pointers.

Choose this experimental backend as a candidate for lookup-heavy workloads,
especially with large values. Compare it with ArrayBased using your actual
value sizes and access patterns; split storage is not automatically better for
small values or frequent updates.

## Configuration example

```zig
const TreeType = zigavl.TreeWithOptions(i64, i64, i64Cmp, .{
    .nodeCacheType = .StableArrayBased,
    .countChildren = true,
});
```

`countChildren` is independent of storage selection. Enable it when positional
access or rank/range queries matter while the tree is being mutated. It stores
subtree counts as `u32`, increases metadata and mutation work, and provides
`O(log n)` positional access. Without counts or valid ordered storage, `rank`,
`rankDistance`, `countInRange`, `at`, `iteratorAt`, and `deleteAt` may scan linearly.
The count representation supports at most `maxInt(u32) + 1` elements; the
address-based caches have their own 32-bit slot limit with a reserved invalid
address. Retained free slots consume that address space too.

## Reserving capacity

`try tree.ensureCapacity(n)` reserves node storage for at least `n` live
elements in ArrayBased, StableArrayBased, and SplitArrayBased. This is a total
element count, not a count of additional insertions. Existing free slots count
toward the reservation. Smaller or repeated requests do not shrink storage;
keys, values, length, and ordered-storage state remain unchanged.

```zig
var tree = try TreeType.init(allocator);
defer tree.deinit();
try tree.ensureCapacity(100_000);
```

After success, insertion up to that live count needs no further node-storage
allocations, including when deleted slots are reused. Constructors supplied to
`getOrEmplace` may still allocate themselves. `clear`, `compactStorage`,
`orderStorageByKey`, and `buildFromSorted` may discard reserved capacity; reserve
again afterward if needed.
`clearRetainingCapacity()` preserves the reservation for the next fill.

Growth can invalidate value pointers for ArrayBased and SplitArrayBased, even
if a later allocation fails. StableArrayBased keeps existing value pointers.
An allocation failure returns `error.OutOfMemory` and preserves tree contents,
but some storage may already have grown. Requests beyond the backend's 32-bit
slot limit also return `error.OutOfMemory`.

PointerBased allocates each node separately and cannot provide this guarantee.
Calling `ensureCapacity` on it produces a compile error; other operations remain
available. Internally, `cache.getCapabilities(Cache).hasReserveNodes` checks
support for the concrete cache type. The optional cache method
`reserveNodes(self: *Cache, count: usize) !void` must reserve for `count` further
node creations, including reusable free slots; the tree converts total capacity
to this additional count.

## Bulk loading and read-heavy phases

`buildFromSorted(items)` replaces the contents from strictly sorted, unique
`KV` items in `O(n)`. Duplicate or unordered keys return
`error.ItemsNotStrictlySorted` before clearing the existing tree. PointerBased
uses an `O(n)` temporary location list; address-based backends use `O(1)`
auxiliary memory and immediately store the new nodes in key order. Failure to
allocate the pointer-backend location list preserves the tree; an allocation
failure after replacement starts leaves the tree empty.

For an existing tree that will be queried many times, consider
`orderStorageByKey()`. It orders supported address-based storage in `O(n)` and
may invalidate iterators, locations, entries, and value pointers. PointerBased
treats it as a no-op.

While the ordered layout remains valid:

- `get`, `lowerBound`, `upperBound`, `rank`, `rankDistance`, and `countInRange`
  use binary search over dense storage in `O(log n)`.
- `at`, `iteratorAt`, and the position-resolution part of `deleteAt` are `O(1)`.
  Deleting/rebalancing the selected node can still take `O(log n)`.
- Iterator `next`/`prev` advances through adjacent slots in `O(1)`.

Appending a new maximum or removing the current maximum preserves ordering.
Other structural mutations invalidate this layout; ordering is not maintained
by shifting storage on each insertion. Include the one-time ordering cost in
your workload comparison. For a build-once/read-many phase, ordered storage may
make subtree counts unnecessary for fast positional reads.

## Removing the first or last element

`popFirst()` and `popLast()` remove and return the first or last `KV` pair in
comparator order, or `null` when the tree is empty. With a reversed comparator,
the first key is the numerically largest key. `KV.Value` is the stored value,
not a pointer into the node being removed.

Both methods call the shared deletion implementation using the cached minimum
or maximum location. They perform no key comparisons or search from the root;
AVL rebalancing, updating extrema, and subtree-count maintenance can still take
`O(log n)`. They are available on all backends.

`delete(key)` also predicts consecutive removals from an edge. After deleting
a minimum or maximum it first checks the current edge in that direction; a
match avoids root search, while a miss disables the hint and uses ordinary
lookup. Interior deletion disables the hint as well. This uses one key
comparison for continued edge runs; the explicit pop methods use none. See the
[adaptive-delete measurements](bench-adaptive-delete.md) for gains and overhead.

For ordered address-based storage, popping the last element preserves ordering
while the tree remains nonempty. Popping the first element of a multi-element
tree invalidates the ordered-storage fast path, as ordinary deletion does.
`deleteAt(0)` and `deleteAt(len() - 1)` also resolve an edge directly, but require
a nonempty tree; the pop methods handle emptiness with an optional result.

## Memory maintenance and lifetime

`compactStorage()` compacts address-based storage after deletions. ArrayBased
and SplitArrayBased can shrink backing arrays; StableArrayBased can free unused
tail chunks. It may move live nodes and invalidates the ordered-storage fast
path. PointerBased treats it as a no-op. Use it after a large reduction in live
nodes when reclaiming storage matters more than keeping references stable.

`clear()` removes every element and releases node storage owned by the tree:
`O(n)` for PointerBased, `O(1)` for ArrayBased/SplitArrayBased, and
`O(number of chunks)` for StableArrayBased, in terms of storage operations.
It does not retain array capacity for the next fill. Actual memory release
behavior also depends on the allocator.

`clearRetainingCapacity()` removes every element while retaining all allocated
arrays and chunks, including capacity reserved by `ensureCapacity`. It performs
no allocations or frees and takes `O(1)` for ArrayBased, SplitArrayBased, and
StableArrayBased. Repeated clearing of an empty tree also retains its capacity.
It resets the free list and ordered-storage state; later insertions start at
the beginning of storage. For PointerBased, it frees nodes in `O(n)` like
`clear()`, even when fast deinit is enabled.

Use it between batches when memory reuse matters; use `clear()` to release
storage. Both methods invalidate all previous entries, value pointers,
locations, and iterators. They do not release resources owned by keys or values;
clean those up before clearing if needed. Retained capacity is released by
`clear()` or `deinit()` and may be reduced by other storage maintenance.

For arenas or fixed buffers, `initWithOptions(..., .{ .allowFastDeinit = .auto })`
can avoid per-node destruction when the backend recognizes that allocator.
`.always` skips node destruction unconditionally: use it only when the memory
will be reclaimed by the allocator owner. Backend-owned storage cleanup still
runs. This option affects `deinit`, not the semantics of `clear` or
`clearRetainingCapacity`.

## Measuring the tradeoffs

Compare live and peak element counts, allocation behavior, pointer lifetimes,
key comparison cost, payload sizes, and the ratio of reads to mutations.
Use the [benchmark guide](benchmarks.md) to select relevant scenarios. See the
[node-layout experiment](bench-node-layout.md) for one measured example of
padding savings; its byte counts and timings depend on types and hardware.
