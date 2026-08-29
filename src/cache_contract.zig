pub fn Meta(comptime Tags: type) type {
    return struct {
        height: *u8,
        tags: *Tags,
    };
}

// Capabilities is computed from a concrete cache implementation and describes
// optional cache operations that the tree can use when they are available.
pub const Capabilities = struct {
    hasFastClear: bool,
    hasCompactStorage: bool,
    hasOrderedStorage: bool,
};

pub fn getCapabilities(comptime Cache: type) Capabilities {
    return .{
        .hasFastClear = @hasDecl(Cache, "clearAll"),
        .hasCompactStorage = @hasDecl(Cache, "reclaim"),
        .hasOrderedStorage = @hasDecl(Cache, "relocate") and
            @hasDecl(Cache, "finishOrderStorage") and
            @hasDecl(Cache, "locationAt") and
            @hasDecl(Cache, "nextLocation") and
            @hasDecl(Cache, "prevLocation"),
    };
}
