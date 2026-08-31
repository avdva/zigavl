const std = @import("std");

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

const fast_deinit_alloc_addrs = blk: {
    var arena: std.heap.ArenaAllocator = undefined;
    const arena_allocator = arena.allocator();
    var fixed_buffer: std.heap.FixedBufferAllocator = undefined;
    const fixed_buffer_allocator = fixed_buffer.allocator();
    break :blk [_]*const anyopaque{
        @ptrCast(@alignCast(arena_allocator.vtable.alloc)),
        @ptrCast(@alignCast(fixed_buffer_allocator.vtable.alloc)),
    };
};

// fastDeinitAllowed returns true for allocators that can release all tree-owned
// node memory at once, so the tree can skip walking and destroying every node.
pub fn fastDeinitAllowed(a: std.mem.Allocator) bool {
    const alloc_addr: *const anyopaque = @ptrCast(@alignCast(a.vtable.alloc));
    inline for (fast_deinit_alloc_addrs) |ptr| {
        if (alloc_addr == ptr) return true;
    }
    return false;
}

test "fastDeinitAllowed ArenaAllocator" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    try std.testing.expect(fastDeinitAllowed(arena.allocator()));
    defer arena.deinit();
}

test "fastDeinitAllowed FixedBufferAllocator" {
    var buff: [16 * 1024]u8 = undefined;
    var fb = std.heap.FixedBufferAllocator.init(&buff);
    try std.testing.expect(fastDeinitAllowed(fb.allocator()));
}

test "fastDeinitAllowed std.testing.allocator" {
    try std.testing.expect(!fastDeinitAllowed(std.testing.allocator));
}
