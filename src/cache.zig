const arrayLocationCache = @import("array_location.zig").LocationCache;
const ptrLocationCache = @import("pointer_location.zig").LocationCache;
const stableArrayLocationCache = @import("stable_array_location.zig").LocationCache;

// NodeCacheType selects how tree nodes are stored.
pub const NodeCacheType = enum(u8) {
    // PointerBased allocates each node separately through the provided allocator.
    // It keeps value pointers stable across future insertions and is the most
    // conservative default backend.
    PointerBased,

    // ArrayBased stores nodes in a contiguous ArrayList-backed slot cache.
    // It usually has good locality and compact node links, but future insertions
    // may reallocate the backing array and invalidate previously returned *V pointers.
    ArrayBased,

    // StableArrayBased stores nodes in fixed-size chunks addressed by compact u32
    // handles. It keeps value pointers stable across future insertions; chunks are
    // kept until deinit(), so memory usage can grow to the peak node count.
    StableArrayBased,
};

// Capabilities is a struct that is computed based on the actual cache
// implementation and contains flags that enable additional operations
// on the cache.
pub const Capabilities = struct {
    hasFastClear: bool,
    hasCompactStorage: bool,
    hasOrderedStorage: bool,
};

// Create returns cache type of given type.
pub fn Create(
    comptime nodeCacheType: NodeCacheType,
    comptime K: type,
    comptime V: type,
    comptime Tags: type,
) type {
    return switch (nodeCacheType) {
        .ArrayBased => arrayLocationCache(K, V, Tags),
        .PointerBased => ptrLocationCache(K, V, Tags),
        .StableArrayBased => stableArrayLocationCache(K, V, Tags),
    };
}

// getCapabilities computes and returns capabilities for given cache.
pub fn getCapabilities(comptime Cache: type) Capabilities {
    return Capabilities{
        .hasFastClear = @hasDecl(Cache, "clearAll"),
        .hasCompactStorage = @hasDecl(Cache, "reclaim"),
        .hasOrderedStorage = @hasDecl(Cache, "relocate") and
            @hasDecl(Cache, "finishOrderStorage") and
            @hasDecl(Cache, "locationAt") and
            @hasDecl(Cache, "nextLocation") and
            @hasDecl(Cache, "prevLocation"),
    };
}
