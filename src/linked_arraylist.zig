const std = @import("std");
const mem = std.mem;
const math = std.math;
const Allocator = mem.Allocator;
const testing = std.testing;
const assert = std.debug.assert;

pub const Address = u32;

pub const InvalidAddr = math.maxInt(Address);

pub const Error = error{
    InvalidCapacity,
    InvalidWatermarks,
};

pub const Options = struct {
    // InfiniteWatermark is a special value for loadHighWatermark.
    // When set, the free list size is not limited and the memory is never released.
    pub const InfiniteWatermark: u16 = math.maxInt(u16);
    // capacity is the initial capacity of the list.
    // The underlying list's capacity is set to this value each time clear() is called.
    capacity: usize = 16,
    // allowRelocations, if set, allows LinkedArrayList to relocate nodes in the list,
    // invalidating pointers to those nodes.
    // When a node is removed at the position which is not the last physical position of the list,
    // the node from the last physical position will be relocated to this position.
    // The nodes at the end of the list will be reused for newly added items.
    // When an relocation happens, relocCallbackFn, if set, will be called with relocCallbackCtx
    // and two addresses: source and destination addresses of the relocation.
    // If allowRelocations is not set, the nodes of the removed elements form a free-list and will be reused
    // for newly added elements.
    // If relocations are allowed, the list may shrink the size of underlying list to save memory.
    // There are two parameters to control memory reclaims: loadHighWatermark, loadLowWatermark.
    // Consider
    // loadFactor allows to specify maximum free list size to the list size ratio (in percentage, e.g. 10):
    //                 free_list_size
    //  loadFactor = ------------------- * 100
    //                    list_size
    // Then:
    //  - loadHighWatermark is the upper limit for the loadFactor. When it's reached, the unused memory will be freed.
    //  - loadLowWatermark if the target value for loadFactor when the memory is being released. Must be <= loadHighWatermark.
    allowRelocations: bool = false,
    // loadHighWatermark is the upper limit for the loadFactor.
    loadHighWatermark: u16 = 10,
    // loadLowWatermark if the target value for loadFactor when the memory is being released
    loadLowWatermark: u16 = 5,
    // relocCallbackFn, if set will be called each time a relocation happens.
    //  ctx - the context to be passed to the callback.
    //  from - the address where the node was located.
    //  to - the new address of the node.
    relocCallbackFn: ?*const fn (ctx: *anyopaque, from: Address, to: Address) void = null,
    // relocCallbackCtx is an arbitrary user-defined value to be passed to relocCallbackFn.
    relocCallbackCtx: *anyopaque = undefined,
};

pub fn LinkedArrayList(comptime T: type) type {
    return struct {
        const Node = struct {
            elem: T,
            left: Address,
            right: Address,
        };

        const Self = @This();

        free_list_size: usize,
        free_list_tail: Address,
        head_addr: Address,
        tail_addr: Address,
        length: usize,
        options: Options,
        list: std.ArrayList(Node),
        allocator: Allocator,

        fn validateOptions(options: Options) !void {
            if (options.capacity > math.maxInt(Address)) {
                return Error.InvalidCapacity;
            }
            if (options.allowRelocations) {
                if (options.loadLowWatermark > options.loadHighWatermark) {
                    return Error.InvalidWatermarks;
                }
            }
        }

        pub fn initOptions(allocator: Allocator, options: Options) !Self {
            try validateOptions(options);
            return Self{
                .free_list_tail = InvalidAddr,
                .free_list_size = 0,
                .head_addr = InvalidAddr,
                .tail_addr = InvalidAddr,
                .length = 0,
                .options = options,
                .allocator = allocator,
                .list = try std.ArrayList(Node).initCapacity(allocator, options.capacity),
            };
        }

        pub fn fromSlice(a: mem.Allocator, slice: []const T) !Self {
            var al = try Self.initOptions(a, .{});
            errdefer al.deinit();
            for (slice) |val| {
                _ = try al.push(val);
            }
            return al;
        }

        pub fn fromArray(a: mem.Allocator, comptime N: usize, array: [N]T) !Self {
            return fromSlice(a, array[0..]);
        }

        pub fn toOwnedSlice(self: *Self) ![]T {
            var slice = try self.allocator.alloc(T, self.len());
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
            self.list.deinit(self.allocator);
        }

        pub fn len(self: *const Self) usize {
            return self.length;
        }

        // clear removes all elements from the list.
        pub fn clear(self: *Self) void {
            self.free_list_tail = InvalidAddr;
            self.free_list_size = 0;
            self.head_addr = InvalidAddr;
            self.tail_addr = InvalidAddr;
            self.length = 0;
            self.shrinkTo(0);
        }

        pub fn eq(self: *Self, other: *Self) bool {
            if (self.len() != other.len()) {
                return false;
            }
            var it1 = self.iterator();
            var it2 = other.iterator();
            while (it1.value()) |val1| {
                const val2 = it2.value().?;
                if (val1.* != val2.*) {
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
                try self.list.append(self.allocator, new_node);
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

        fn addToFreeList(self: *Self, addr: Address) void {
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
                assert(addr == self.head_addr);
                self.head_addr = node.right;
            }

            self.length -= 1;

            self.itemRemovedAt(addr);

            return elem;
        }

        fn itemRemovedAt(self: *Self, addr: Address) void {
            if (self.options.allowRelocations) {
                const last_item_addr = @as(Address, @intCast(self.length));
                self.relocate(last_item_addr, addr);
                self.addToFreeList(last_item_addr);
                self.checkLoadFactor();
            } else {
                self.addToFreeList(addr);
            }
        }

        fn checkLoadFactor(self: *Self) void {
            const length = self.length;
            if (self.options.loadHighWatermark == Options.InfiniteWatermark) {
                return;
            }
            if (length == 0) {
                self.shrinkTo(0);
                return;
            }
            const current_ratio: usize = self.free_list_size * 100 / length;
            if (current_ratio < self.options.loadHighWatermark) {
                return;
            }
            const new_len: usize = length + length * self.options.loadLowWatermark / 100;
            self.shrinkTo(new_len);
        }

        // shrinkTo shrinks the underlying arraylist to `new_len` length.
        // it always retains the capacity specified in the options.
        fn shrinkTo(self: *Self, new_len: usize) void {
            if (new_len >= self.list.items.len) {
                return;
            }
            if (new_len > self.options.capacity) {
                self.list.shrinkAndFree(self.allocator, new_len);
            } else {
                self.list.shrinkRetainingCapacity(new_len);
            }
            self.free_list_size = @max(new_len - self.length, 0);
            if (self.free_list_size > 0) {
                const last_free_list_item_addr = @as(Address, @intCast(new_len - 1));
                self.list.items[last_free_list_item_addr].left = InvalidAddr;
            } else {
                self.free_list_tail = InvalidAddr;
            }
        }

        // relocate relocated data from `from` address to `to` address.
        // relocation callback is called if the move has happened (i.e. if addr != address of the last item).
        fn relocate(self: *Self, from: Address, to: Address) void {
            if (from != to) {
                self.relocateAtAddress(from, to);
                if (self.options.relocCallbackFn) |cb| {
                    cb(self.options.relocCallbackCtx, from, to);
                }
            }
        }

        // relocateAtAddress relocates data from the `from` address to `to`.
        // assumes that the the items at both addresses are not in the free list.
        fn relocateAtAddress(self: *Self, from: Address, to: Address) void {
            const fromNode = &self.list.items[from];
            const toNode = &self.list.items[to];
            toNode.* = fromNode.*;
            if (toNode.left != InvalidAddr) {
                assert(self.list.items[toNode.left].right == from);
                self.list.items[toNode.left].right = to;
            }
            if (toNode.right != InvalidAddr) {
                assert(self.list.items[toNode.right].left == from);
                self.list.items[toNode.right].left = to;
            }
            if (self.head_addr == from) {
                self.head_addr = to;
            }
            if (self.tail_addr == from) {
                self.tail_addr = to;
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

test "LinkedArrayList eq compares with other list" {
    const a = testing.allocator;
    var left = try LinkedArrayList(i32).fromArray(a, 3, [_]i32{ 1, 2, 3 });
    defer left.deinit();
    var same = try LinkedArrayList(i32).fromArray(a, 3, [_]i32{ 1, 2, 3 });
    defer same.deinit();
    var different = try LinkedArrayList(i32).fromArray(a, 3, [_]i32{ 1, 9, 3 });
    defer different.deinit();
    var shorter = try LinkedArrayList(i32).fromArray(a, 2, [_]i32{ 1, 2 });
    defer shorter.deinit();

    try testing.expect(left.eq(&same));
    try testing.expect(!left.eq(&different));
    try testing.expect(!left.eq(&shorter));
}

test "LinkedArrayList rejects invalid options" {
    const a = testing.allocator;

    try testing.expectError(
        Error.InvalidWatermarks,
        LinkedArrayList(i32).initOptions(a, .{
            .allowRelocations = true,
            .loadHighWatermark = 10,
            .loadLowWatermark = 20,
        }),
    );
    try testing.expectError(
        Error.InvalidCapacity,
        LinkedArrayList(i32).initOptions(a, .{
            .capacity = @as(usize, math.maxInt(Address)) + 1,
        }),
    );
}

fn calculateListLengthFromTail(comptime T: type, start: Address, list: *LinkedArrayList(T)) usize {
    var length: usize = 0;
    var addr = start;
    while (addr != InvalidAddr) {
        const node = &list.list.items[addr];
        addr = node.left;
        length += 1;
    }
    return length;
}

fn calculateListLengthFromHead(comptime T: type, start: Address, list: *LinkedArrayList(T)) usize {
    var length: usize = 0;
    var addr = start;
    while (addr != InvalidAddr) {
        const node = &list.list.items[addr];
        addr = node.right;
        length += 1;
    }
    return length;
}

fn expectListInvariants(comptime T: type, list: *LinkedArrayList(T)) !void {
    try testing.expectEqual(list.length, calculateListLengthFromHead(T, list.head_addr, list));
    try testing.expectEqual(list.length, calculateListLengthFromTail(T, list.tail_addr, list));
    try testing.expectEqual(list.free_list_size, calculateListLengthFromTail(T, list.free_list_tail, list));
    if (list.length == 0) {
        try testing.expectEqual(InvalidAddr, list.head_addr);
        try testing.expectEqual(InvalidAddr, list.tail_addr);
    } else {
        try testing.expect(list.head_addr != InvalidAddr);
        try testing.expect(list.tail_addr != InvalidAddr);
    }
    if (list.free_list_size == 0) {
        try testing.expectEqual(InvalidAddr, list.free_list_tail);
    } else {
        try testing.expect(list.free_list_tail != InvalidAddr);
    }
}

test "LinkedArrayList ensure list size and free list sizes are correct" {
    const total_size: usize = 128;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{
        .loadHighWatermark = Options.InfiniteWatermark,
        .allowRelocations = true,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    // add elements 0..127 to the list
    while (i < total_size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }

    i = 0;
    while (i < total_size) : (i += 1) {
        try std.testing.expectEqual(@as(usize, @intCast(i)), calculateListLengthFromTail(i32, la.free_list_tail, &la));
        try std.testing.expectEqual(total_size - @as(usize, @intCast(i)), calculateListLengthFromHead(i32, la.head_addr, &la));
        try std.testing.expectEqual(total_size - @as(usize, @intCast(i)), calculateListLengthFromTail(i32, la.tail_addr, &la));
        _ = la.pop_head();
    }

    i = 0;
    while (i < total_size) : (i += 1) {
        try std.testing.expectEqual(total_size - @as(usize, @intCast(i)), calculateListLengthFromTail(i32, la.free_list_tail, &la));
        try std.testing.expectEqual(@as(usize, @intCast(i)), calculateListLengthFromHead(i32, la.head_addr, &la));
        try std.testing.expectEqual(@as(usize, @intCast(i)), calculateListLengthFromTail(i32, la.tail_addr, &la));
        _ = try la.push(i);
    }
}

test "LinkedArrayList relocate partial shrink keeps free list valid" {
    const total_size: usize = 100;
    const a = testing.allocator;
    var la = LinkedArrayList(i32).initOptions(a, .{
        .capacity = 0,
        .allowRelocations = true,
        .loadHighWatermark = 50,
        .loadLowWatermark = 25,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();

    for (0..total_size) |idx| {
        _ = try la.push(@intCast(idx));
    }
    try expectListInvariants(i32, &la);

    var deletes: usize = 0;
    while (deletes < 34) : (deletes += 1) {
        _ = la.pop_head();
        try expectListInvariants(i32, &la);
    }

    try testing.expectEqual(@as(usize, 66), la.len());
    try testing.expectEqual(@as(usize, 82), la.list.items.len);
    try testing.expectEqual(@as(usize, 16), la.free_list_size);
    try expectListInvariants(i32, &la);
}

test "LinkedArrayList relocate, never free memory" {
    const total_size: usize = 128;
    var current_size: usize = total_size;
    const a = testing.allocator;
    var rcb = reallocHelper{};
    var la = LinkedArrayList(i32).initOptions(a, .{
        .loadHighWatermark = Options.InfiniteWatermark,
        .allowRelocations = true,
        .relocCallbackCtx = &rcb,
        .relocCallbackFn = reallocHelper.cb,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    // add elements 0..127 to the list
    while (i < current_size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(current_size, la.len());
    try std.testing.expectEqual(total_size - current_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    current_size -= 1;

    // pop tail, no relocation should happen
    var removed: i32 = la.pop_tail();
    try std.testing.expectEqual(127, removed);
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(current_size, la.len());
    try std.testing.expectEqual(total_size - current_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    current_size -= 1;

    // pop head, the new head should be at position 1, and the last item should
    // be relocated to position 0.
    removed = la.pop_head();
    try std.testing.expectEqual(0, removed);
    try std.testing.expectEqual(126, rcb.actFrom);
    try std.testing.expectEqual(0, rcb.actTo);
    try std.testing.expectEqual(current_size, la.len());
    try std.testing.expectEqual(total_size - current_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    current_size -= 1;

    // remove elements in the middle of the list. this should always cause relocations.
    while (la.len() > 2) {
        const l = la.len();
        const addr = @as(Address, @intCast(l / 2));
        rcb.reset();
        _ = la.deleteAtAddr(addr);
        // exactly one call should be made and an item from the last address should be relocated to `addr`.
        try std.testing.expectEqual(1, rcb.calls);
        try std.testing.expectEqual(addr, rcb.actTo.?);
        try std.testing.expectEqual(l - 1, rcb.actFrom.?);
        try std.testing.expectEqual(current_size, la.len());
        try std.testing.expectEqual(total_size - current_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));
        current_size -= 1;
    }
    // now we have the following list:
    // logical:  65 -> 126
    // physical: 126 -> 65
    // if we remove the tail, a relocation should happen.
    rcb.reset();
    removed = la.pop_tail();
    try std.testing.expectEqual(126, removed);
    try std.testing.expectEqual(1, rcb.calls);
    try std.testing.expectEqual(1, rcb.actFrom);
    try std.testing.expectEqual(0, rcb.actTo);
    try std.testing.expectEqual(1, la.len());
    try std.testing.expectEqual(total_size - current_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    // finally, remove the last element
    rcb.reset();
    removed = la.pop_tail();
    try std.testing.expectEqual(65, removed);
    try std.testing.expectEqual(0, rcb.calls);
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(0, la.len());
    try std.testing.expectEqual(total_size, calculateListLengthFromTail(i32, la.free_list_tail, &la));

    la.clear();
    try std.testing.expectEqual(0, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
}

test "LinkedArrayList relocate, free memory every call to remove" {
    var size: usize = 128;
    const a = testing.allocator;
    var rcb = reallocHelper{};
    var la = LinkedArrayList(i32).initOptions(a, .{
        .loadHighWatermark = 0,
        .loadLowWatermark = 0,
        .allowRelocations = true,
        .relocCallbackCtx = &rcb,
        .relocCallbackFn = reallocHelper.cb,
    }) catch |err| {
        std.debug.panic("Failed to init LinkedArrayList: {}", .{err});
    };
    defer la.deinit();
    var i: i32 = 0;
    // add elements 0..127 to the list
    while (i < size) : (i += 1) {
        const addr = try la.push(i);
        try testing.expectEqual(i, la.get(addr));
    }
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(size, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    size -= 1;

    // pop tail, no relocation should happen
    var removed: i32 = la.pop_tail();
    try std.testing.expectEqual(127, removed);
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(size, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    size -= 1;

    // pop head, the new head should be at position 1, and the last item should
    // be relocated to position 0.
    removed = la.pop_head();
    try std.testing.expectEqual(0, removed);
    try std.testing.expectEqual(126, rcb.actFrom);
    try std.testing.expectEqual(0, rcb.actTo);
    try std.testing.expectEqual(size, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    size -= 1;

    // remove elements in the middle of the list. this should always cause relocations.
    while (la.len() > 2) {
        const l = la.len();
        const addr = @as(Address, @intCast(l / 2));
        rcb.reset();
        _ = la.deleteAtAddr(addr);
        // exactly one call should be made and an item from the last address should be relocated to `addr`.
        try std.testing.expectEqual(1, rcb.calls);
        try std.testing.expectEqual(addr, rcb.actTo.?);
        try std.testing.expectEqual(l - 1, rcb.actFrom.?);
        try std.testing.expectEqual(size, la.len());
        try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
        size -= 1;
    }
    // now we have the following list:
    // logical:  65 -> 126
    // physical: 126 -> 65
    // if we remove the tail, a relocation should happen.
    rcb.reset();
    removed = la.pop_tail();
    try std.testing.expectEqual(126, removed);
    try std.testing.expectEqual(1, rcb.calls);
    try std.testing.expectEqual(1, rcb.actFrom);
    try std.testing.expectEqual(0, rcb.actTo);
    try std.testing.expectEqual(1, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
    // finally, remove the last element
    rcb.reset();
    removed = la.pop_tail();
    try std.testing.expectEqual(65, removed);
    try std.testing.expectEqual(0, rcb.calls);
    try std.testing.expectEqual(null, rcb.actFrom);
    try std.testing.expectEqual(null, rcb.actTo);
    try std.testing.expectEqual(0, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));

    la.clear();
    try std.testing.expectEqual(0, la.len());
    try std.testing.expectEqual(0, calculateListLengthFromTail(i32, la.free_list_tail, &la));
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
