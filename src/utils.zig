const std = @import("std");

const allocAddrs = blk: {
    var aa: std.heap.ArenaAllocator = undefined;
    const aaa = aa.allocator();
    var fba: std.heap.FixedBufferAllocator = undefined;
    const fbaa = fba.allocator();
    break :blk [_]*const anyopaque{
        @ptrCast(@alignCast(aaa.vtable.alloc)),
        @ptrCast(@alignCast(fbaa.vtable.alloc)),
    };
};

pub fn fastDeinitAllowed(a: std.mem.Allocator) bool {
    const ourAllocAddr: *const anyopaque = @ptrCast(@alignCast(a.vtable.alloc));
    inline for (allocAddrs) |ptr| {
        if (ourAllocAddr == ptr) return true;
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
