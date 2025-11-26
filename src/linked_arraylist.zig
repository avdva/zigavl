const std = @import("std");
const mem = std.mem;
const math = std.math;
const Allocator = mem.Allocator;
const testing = std.testing;
const assert = std.debug.assert;

pub const Address = u32;
pub const InvalidAddr = math.maxInt(Address);

pub const Options = struct {
    pub const UnlimitedFreeListSize: u16 = math.maxInt(u16);
    cap: usize = 16,
    // loadFactor allows to specify maximum free list size to the list size ratio (in percentage, e.g. 10):
    //                 free_list_size
    //  loadFactor = ------------------- * 100
    //                    list_size
    // when this value is exceeded, the list starts relocations.
    //
    // possible values:
    //
    //  0: disallow free list, always relocate nodes.
    //
    //  1..math.maxInt(u16)-1: ratio value as a percentage. the list will relocate nodes releasing memory,
    //  when the free list size exceeds this percentage of the list size. the relocations will continue until the
    //  free list size is below loadfactor / 2.
    //  for example, with loadFactor = 10, when this value is exceeded, the list will relocate nodes
    //  until the free list size is below 5% of the list size.
    //
    //  math.maxInt(u16):  (default) don't limit free list size (disable relocations).
    loadFactor: u16 = UnlimitedFreeListSize,
    ctx: *anyopaque = undefined,
    relocCb: ?*const fn (ctx: *anyopaque, from: Address, to: Address) void = null,
};

pub fn LinkedArrayList(comptime T: type) type {
    const Node = struct {
        elem: T,
        left: Address,
        right: Address,
    };

    return struct {
        const Self = @This();

        free_list_tail: Address,
        free_list_size: usize,
        head_addr: Address,
        tail_addr: Address,
        length: usize,
        options: Options,
        list: std.ArrayList(Node),
        a: Allocator,

        pub fn initOptions(a: Allocator, options: Options) Allocator.Error!Self {
            return Self{
                .free_list_tail = InvalidAddr,
                .free_list_size = 0,
                .head_addr = InvalidAddr,
                .tail_addr = InvalidAddr,
                .length = 0,
                .options = options,
                .a = a,
                .list = try std.ArrayList(Node).initCapacity(a, options.cap),
            };
        }

        pub fn fromSlice(a: mem.Allocator, slice: []const T) Allocator.Error!Self {
            var al = try Self.initOptions(a, .{});
            errdefer al.deinit();
            for (slice) |val| {
                _ = try al.push(val);
            }
            return al;
        }

        pub fn fromArray(a: mem.Allocator, comptime N: usize, array: [N]T) Allocator.Error!Self {
            return fromSlice(a, array[0..]);
        }

        pub fn toOwnedSlice(self: *Self) Allocator.Error![]T {
            var slice = try self.a.alloc(T, self.len());
            var it = self.iterator();
            var i: usize = 0;
            while (it.value()) |val| {
                slice[i] = val.*;
                i += 1;
                it.next();
            }
            return slice;
        }

        pub fn deinit(self: *Self) void {
            self.list.deinit(self.a);
        }

        pub fn len(self: *const Self) usize {
            return self.length;
        }

        pub fn clear(self: *Self) void {
            self.free_list_tail = InvalidAddr;
            self.free_list_size = 0;
            self.head_addr = InvalidAddr;
            self.tail_addr = InvalidAddr;
            self.length = 0;
            if (self.list.items.len > self.options.cap) {
                self.list.shrinkRetainingCapacity(self.options.cap);
            }
        }

        pub fn eq(self: *Self, other: *Self) bool {
            if (self.len() != other.len()) {
                return false;
            }
            var it1 = self.iterator();
            var it2 = self.iterator();
            while (it1.value()) |val1| {
                const val2 = it2.value().?;
                if (val1 != val2) {
                    return false;
                }
                it1.next();
                it2.next();
            }
            return true;
        }

        pub fn push(self: *Self, elem: T) Allocator.Error!Address {
            var new_node_addr: Address = self.takeNodeFromFreeList();
            const new_node = Node{ .elem = elem, .left = self.tail_addr, .right = InvalidAddr };
            if (new_node_addr != InvalidAddr) { // use a node from the freelist
                self.list.items[new_node_addr] = new_node;
            } else { // append new node.
                new_node_addr = @intCast(self.list.items.len);
                try self.list.append(self.a, new_node);
            }
            if (self.length > 0) { // there was at least one element. update its right index.
                self.list.items[self.tail_addr].right = new_node_addr;
            } else { // the list was empty, we're the new head.
                self.head_addr = new_node_addr;
            }
            self.tail_addr = new_node_addr;
            self.length += 1;
            return new_node_addr;
        }

        fn takeNodeFromFreeList(self: *Self) Address {
            if (self.free_list_size == 0) {
                return InvalidAddr;
            }
            const result = self.free_list_tail;
            self.free_list_tail = self.list.items[self.free_list_tail].left;
            self.free_list_size -= 1;
            return result;
        }

        fn add_to_free_list(self: *Self, addr: Address) void {
            var node = &self.list.items[addr];
            node.right = InvalidAddr;
            if (self.free_list_tail == InvalidAddr) {
                node.left = InvalidAddr;
                self.free_list_tail = addr;
            } else {
                node.left = self.free_list_tail;
                self.free_list_tail = addr;
            }
            self.free_list_size += 1;
        }

        fn posToAddr(self: *Self, pos: Address) Address {
            assert(pos < self.list.items.len);
            var it = self.iterator();
            var i = pos;
            while (true) {
                if (i == 0) {
                    return it.addr;
                }
                it.next();
                i -= 1;
            }
            unreachable;
        }

        pub fn deleteAtPos(self: *Self, pos: Address) T {
            assert(pos < self.len());
            return self.deleteAtAddr(self.posToAddr(pos));
        }

        pub fn deleteAtAddr(self: *Self, addr: Address) T {
            assert(addr < self.list.items.len);

            const node = &self.list.items[addr];
            const elem = node.elem;
            // removing one last head element.
            // just clear the list.
            if (self.len() == 1) {
                assert(node.left == InvalidAddr and node.right == InvalidAddr);
                self.clear();
                return elem;
            }

            // deal with the right neighbor
            if (node.right != InvalidAddr) {
                var right = &self.list.items[node.right];
                assert(right.left == addr);
                right.left = node.left;
            } else { // removing tail
                assert(addr == self.tail_addr);
                self.tail_addr = node.left;
            }

            // deal with the left neighbor
            if (node.left != InvalidAddr) {
                var left = &self.list.items[node.left];
                assert(left.right == addr);
                left.right = node.right;
            } else { // removing head
                var right = &self.list.items[node.right];
                assert(addr == self.head_addr);
                self.head_addr = node.right;
                right.left = InvalidAddr;
            }

            self.itemRemovedAt(addr);

            self.length -= 1;
            return elem;
        }

        fn itemRemovedAt(self: *Self, addr: Address) void {
            switch (self.options.loadFactor) {
                0 => { // no free list, always relocate
                    self.relocateAtAddress(addr);
                },
                Options.UnlimitedFreeListSize => { // unlimited free list size, never relocate
                    self.add_to_free_list(addr);
                },
                else => { // relocate based on load factor
                    self.add_to_free_list(addr);
                    const target_ratio = @as(f64, @floatFromInt(self.options.loadFactor)) / 200.0;
                    while (self.free_list_size > 0) {
                        const current_ratio: f64 = (@as(f64, @floatFromInt(self.free_list_size)) /
                            @as(f64, @floatFromInt(self.length)));
                        if (current_ratio <= target_ratio) {
                            break;
                        }
                        const free_addr = self.takeNodeFromFreeList();
                        self.relocateAtAddress(free_addr);
                    }
                },
            }
        }

        fn relocateAtAddress(self: *Self, addr: Address) void {
            const last_addr = @as(Address, @intCast(self.list.items.len)) - 1;
            if (addr != last_addr) {
                self.doRelocateAtAddress(addr);
            }
            _ = self.list.pop();
            if (self.options.relocCb) |cb| {
                cb(self.options.ctx, last_addr, addr);
            }
        }

        fn doRelocateAtAddress(self: *Self, addr: Address) void {
            const last_addr = @as(Address, @intCast(self.list.items.len)) - 1;
            const lastNode = &self.list.items[last_addr];
            const node = &self.list.items[addr];
            node.* = lastNode.*;
            if (node.left != InvalidAddr) {
                assert(self.list.items[node.left].right == last_addr);
                self.list.items[node.left].right = addr;
            }
            if (node.right != InvalidAddr) {
                assert(self.list.items[node.right].left == last_addr);
                self.list.items[node.right].left = addr;
            }
            if (self.head_addr == last_addr) {
                self.head_addr = addr;
            }
            if (self.tail_addr == last_addr) {
                self.tail_addr = addr;
            }
        }

        pub fn pop_head(self: *Self) T {
            return self.deleteAtAddr(self.head_addr);
        }

        pub fn head(self: *Self) T {
            return self.list.items[self.head_addr].elem;
        }

        pub fn pop_tail(self: *Self) T {
            return self.deleteAtAddr(self.tail_addr);
        }

        pub fn tail(self: *Self) T {
            return self.list.items[self.tail_addr].elem;
        }

        pub fn iterator(self: *Self) Iterator {
            return Iterator{
                .al = self,
                .addr = self.head_addr,
            };
        }

        pub fn deleteIterator(self: *Self, it: Iterator) Iterator {
            std.debug.assert(self == it.al);
            if (it.addr == InvalidAddr) {
                return it;
            }
            const next = self.list.items[it.addr].right;
            _ = self.deleteAtAddr(it.addr);
            return Iterator{
                .al = self,
                .addr = next,
            };
        }

        pub fn get(self: *Self, addr: Address) T {
            return self.list.items[addr].elem;
        }

        pub fn getPtr(self: *Self, addr: Address) *T {
            return &self.list.items[addr].elem;
        }

        pub const Iterator = struct {
            al: *const Self,
            addr: Address,

            pub fn value(self: *const Iterator) ?*T {
                if (self.addr == InvalidAddr) {
                    return null;
                }
                return &self.al.list.items[self.addr].elem;
            }

            pub fn next(self: *Iterator) void {
                if (self.addr != InvalidAddr) {
                    self.addr = self.al.list.items[self.addr].right;
                }
            }
        };
    };
}

test "LinkedArrayList push" {
    const size = 16;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{}) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try testing.expect(la.len() == size);
    var it = la.iterator();
    i = 0;
    while (it.value()) |val| {
        try testing.expect(i == val.*);
        i += 1;
        it.next();
    }
}

test "LinkedArrayList pop_head" {
    const size: usize = 16;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{}) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try testing.expectEqual(size, la.len());
    i = 0;
    while (i < size) : (i += 1) {
        const head_val = la.pop_head();
        try testing.expectEqual(@as(i32, @intCast(i)), head_val);
        try testing.expectEqual(size - 1 - @as(usize, @intCast(i)), la.len());
        var j = i + 1;
        var it = la.iterator();
        while (it.value()) |val| {
            try testing.expectEqual(@as(i32, @intCast(j)), val.*);
            j += 1;
            it.next();
        }
    }
}

test "LinkedArrayList pop_tail" {
    const size = 16;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{}) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try testing.expect(la.len() == size);
    i = 0;
    while (i < size) : (i += 1) {
        const tail_val = la.pop_tail();
        try testing.expectEqual(@as(i32, @intCast(size - i - 1)), tail_val);
        try testing.expectEqual(la.len(), size - 1 - @as(usize, @intCast(i)));
        var j: usize = 0;
        var it = la.iterator();
        while (it.value()) |val| {
            try testing.expectEqual(@as(i32, @intCast(j)), val.*);
            j += 1;
            it.next();
        }
    }
}

test "LinkedArrayList iterator" {
    var a = testing.allocator;
    var slice = [_]i32{ 1, 2, 3, 4, 5, 7, 8 };
    var la = try LinkedArrayList(i32).fromSlice(a, &slice);
    defer la.deinit();
    var start_idx: usize = 0;
    {
        const slice2 = try la.toOwnedSlice();
        defer a.free(slice2);
        try std.testing.expectEqualSlices(i32, slice[start_idx..slice.len], slice2);
    }
    var it = la.iterator();
    try std.testing.expectEqual(@as(i32, 1), it.value().?.*);
    it = la.deleteIterator(it);
    try std.testing.expectEqual(@as(i32, 2), it.value().?.*);
    {
        const act = try la.toOwnedSlice();
        defer a.free(act);
        start_idx = 1;
        try std.testing.expectEqualSlices(i32, slice[start_idx..slice.len], act);
    }
    it.next();
    it.next();
    try std.testing.expectEqual(@as(i32, 4), it.value().?.*);
    it = la.deleteIterator(it);
    try std.testing.expectEqual(@as(i32, 5), it.value().?.*);
    {
        var exp = [_]i32{ 2, 3, 5, 7, 8 };
        const act = try la.toOwnedSlice();
        defer a.free(act);
        try std.testing.expectEqualSlices(i32, @as([]i32, exp[0..exp.len]), act);
    }
    it = la.deleteIterator(it);
    try std.testing.expectEqual(@as(i32, 7), it.value().?.*);
    it = la.deleteIterator(it);
    try std.testing.expectEqual(@as(i32, 8), it.value().?.*);
    it = la.deleteIterator(it);
    try std.testing.expectEqual(@as(?*i32, null), it.value());
    it = la.iterator();
    it.value().?.* = 100;
    try std.testing.expectEqual(@as(i32, 100), la.head());
    while (it.value()) |_| {
        it = la.deleteIterator(it);
    }
    try std.testing.expectEqual(@as(?*i32, null), it.value());
    try std.testing.expectEqual(@as(usize, 0), la.length);
}

test "LinkedArrayList free list" {
    const size = 16;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{}) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try testing.expectEqual(@as(usize, @intCast(size)), la.len());
    try testing.expectEqual(@as(i32, @intCast(0)), la.pop_head());
    try testing.expectEqual(@as(i32, @intCast(15)), la.pop_tail());
    try testing.expectEqual(@as(i32, @intCast(6)), la.deleteAtPos(5));
    try testing.expectEqual(@as(i32, @intCast(10)), la.deleteAtPos(8));
    {
        var exp = try LinkedArrayList(i32).fromSlice(a, &[_]i32{ 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14 });
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
    try testing.expectEqual(@as(usize, @intCast(size - 1)), la.list.items.len);
    _ = try la.push(@as(i32, @intCast(0)));
    _ = try la.push(@as(i32, @intCast(15)));
    _ = try la.push(@as(i32, @intCast(6)));
    _ = try la.push(@as(i32, @intCast(10)));
    _ = try la.push(@as(i32, @intCast(17)));
    try testing.expectEqual(@as(usize, @intCast(17)), la.len());
    {
        var exp = try LinkedArrayList(i32).fromSlice(a, &[_]i32{ 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 0, 15, 6, 10, 17 });
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
    la.clear();
    try testing.expectEqual(@as(usize, @intCast(0)), la.len());
}

test "LinkedArrayList always relocate" {
    const size = 128;
    const a = testing.allocator;
    var rcb = reallocHelper{};
    var la = LinkedArrayList(i32).initOptions(a, .{
        .loadFactor = 0,
        .ctx = &rcb,
        .relocCb = reallocHelper.cb,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);

    _ = la.pop_tail();
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);

    _ = la.pop_head();
    try std.testing.expectEqual(126, rcb.actFrom);
    try std.testing.expectEqual(0, rcb.actTo);

    while (la.len() > 2) {
        rcb.reset();
        const l = la.len();
        const addr = @as(Address, @intCast(l / 2));
        _ = la.deleteAtAddr(addr);
        try std.testing.expectEqual(1, rcb.calls);
        try std.testing.expectEqual(addr, rcb.actTo.?);
        try std.testing.expectEqual(l - 1, rcb.actFrom.?);
    }
}

const reallocHelper = struct {
    actFrom: ?Address = null,
    actTo: ?Address = null,
    calls: usize = 0,

    fn cb(ptr: *anyopaque, from: Address, to: Address) void {
        const self: *reallocHelper = @ptrCast(@alignCast(ptr));
        self.actFrom = from;
        self.actTo = to;
        self.calls += 1;
    }
    fn reset(self: *reallocHelper) void {
        self.actFrom = null;
        self.actTo = null;
        self.calls = 0;
    }
};

test "LinkedArrayList relocate 10pc" {
    const size = 100;
    const a = testing.allocator;
    var rcb = reallocHelper{};
    var la = LinkedArrayList(i32).initOptions(a, .{
        .loadFactor = 10,
        .ctx = &rcb,
        .relocCb = reallocHelper.cb,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    i = 0;
    while (i < size) : (i += 1) {
        _ = la.deleteAtPos(0);
        // try std.testing.expectEqual(@as(?Address, null), rcb.actFrom);
        //try std.testing.expectEqual(@as(?Address, null), rcb.actTo);
        //std.log.warn("xxx {} {}", .{ i, rcb.calls });
    }
    //_ = la.deleteAtPos(0);
    //try std.testing.expectEqual(10, rcb.calls);
}

test "LinkedArrayList remove" {
    const a = testing.allocator;
    var la = try LinkedArrayList(i32).fromArray(a, 5, [_]i32{ 1, 2, 3, 4, 5 });
    defer la.deinit();
    {
        try testing.expectEqual(@as(i32, 2), la.deleteAtPos(1));
        var exp = try LinkedArrayList(i32).fromArray(a, 4, [_]i32{ 1, 3, 4, 5 });
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }

    {
        try testing.expectEqual(@as(i32, 3), la.deleteAtPos(1));
        var exp = try LinkedArrayList(i32).fromArray(a, 3, [_]i32{ 1, 4, 5 });
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
    {
        try testing.expectEqual(@as(i32, 1), la.deleteAtPos(0));
        var exp = try LinkedArrayList(i32).fromArray(a, 2, [_]i32{ 4, 5 });
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
    {
        try testing.expectEqual(@as(i32, 5), la.deleteAtPos(1));
        var exp = try LinkedArrayList(i32).fromArray(a, 1, [_]i32{4});
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
    {
        try testing.expectEqual(@as(i32, 4), la.deleteAtPos(0));
        var exp = try LinkedArrayList(i32).fromArray(a, 0, [_]i32{});
        defer exp.deinit();
        try testing.expect(la.eq(&exp));
    }
}
