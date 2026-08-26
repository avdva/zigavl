const std = @import("std");

pub const Address = u32;
pub const InvalidAddr = std.math.maxInt(Address);

pub fn MakeSlot(comptime Node: type) type {
    return union(enum) {
        used: Node,
        free: Address,
    };
}

fn isFree(cache: anytype, addr: Address) bool {
    return cache.slotAt(addr).* == .free;
}

fn nextFree(cache: anytype, addr: Address) Address {
    return cache.slotAt(addr).free;
}

fn movedAddress(anchor: ?Address, addr_1: Address, addr_2: Address) ?Address {
    const addr = anchor orelse return null;
    if (addr == addr_1) {
        return addr_2;
    }
    if (addr == addr_2) {
        return addr_1;
    }
    return addr;
}

fn relocateStream(cache: anytype, stream1: anytype, stream2: anytype, anchor: ?Address) ?Address {
    var new_anchor = anchor;
    while (true) {
        const addr_1: Address = stream1.next() orelse break;
        const addr_2: Address = stream2.next() orelse break;
        swapAtAddresses(cache, addr_1, addr_2);
        new_anchor = movedAddress(new_anchor, addr_1, addr_2);
    }
    return new_anchor;
}

pub fn swapAtAddresses(cache: anytype, addr_1: Address, addr_2: Address) void {
    const ptr_1 = cache.slotAt(addr_1);
    const ptr_2 = cache.slotAt(addr_2);
    if (ptr_1.* == .free) {
        if (ptr_2.* == .free) {
            return;
        }
        ptr_1.* = ptr_2.*;
        ptr_2.* = .{ .free = InvalidAddr };
        updateLinks(cache, addr_2, addr_1);
        return;
    }
    if (ptr_2.* == .free) {
        ptr_2.* = ptr_1.*;
        ptr_1.* = .{ .free = InvalidAddr };
        updateLinks(cache, addr_1, addr_2);
        return;
    }
    std.mem.swap(@TypeOf(ptr_1.*), ptr_1, ptr_2);
    updateLinks(cache, addr_2, addr_1);
    updateLinks(cache, addr_1, addr_2);
}

pub fn relocate(cache: anytype, addr: Address, target_addr: Address) Address {
    if (addr == InvalidAddr or addr == target_addr) {
        return addr;
    }
    swapAtAddresses(cache, addr, target_addr);
    return target_addr;
}

fn updateLinks(cache: anytype, addr: Address, new_addr: Address) void {
    const node_ptr = &cache.slotAt(new_addr).used;
    if (node_ptr.left != InvalidAddr) {
        if (node_ptr.left == new_addr) {
            node_ptr.left = addr;
        } else {
            cache.slotAt(node_ptr.left).used.parent = new_addr;
        }
    }
    if (node_ptr.right != InvalidAddr) {
        if (node_ptr.right == new_addr) {
            node_ptr.right = addr;
        } else {
            cache.slotAt(node_ptr.right).used.parent = new_addr;
        }
    }
    if (node_ptr.parent != InvalidAddr) {
        if (node_ptr.parent == new_addr) {
            node_ptr.parent = addr;
        } else {
            const parent_ptr = &cache.slotAt(node_ptr.parent).used;
            if (parent_ptr.left == addr) {
                parent_ptr.left = new_addr;
            } else if (parent_ptr.right == addr) {
                parent_ptr.right = new_addr;
            } else {
                unreachable;
            }
        }
    }
}

// UsedSlotsLocator scans the tail part of address storage and yields occupied
// addresses that must be moved into free slots in the compact prefix. It walks
// storage directly because the tail may contain both used and free slots after
// arbitrary delete patterns.
pub fn UsedSlotsLocator(comptime CachePtr: type) type {
    return struct {
        const Self = @This();

        start_address: ?Address,
        current_address: ?Address,
        cache: CachePtr,

        pub fn init(cache: CachePtr, address: Address) Self {
            return .{
                .cache = cache,
                .start_address = address,
                .current_address = null,
            };
        }

        pub fn next(self: *Self) ?Address {
            var address: Address = undefined;
            if (self.current_address == null) {
                address = self.start_address orelse return null;
                self.start_address = null;
            } else {
                address = self.current_address.?;
            }
            while (address < self.cache.slotsLen()) {
                if (!isFree(self.cache, address)) {
                    self.current_address = address + 1;
                    return address;
                }
                address += 1;
            }
            self.current_address = null;
            return null;
        }
    };
}

// FreeListSlotsLocator walks the existing free-list and yields only free slots
// inside [0..end_address). Free nodes outside that prefix are already in the
// part that will be removed from the logical storage length.
pub fn FreeListSlotsLocator(comptime CachePtr: type) type {
    return struct {
        const Self = @This();

        end_address: Address,
        next_address: ?Address = null,
        cache: CachePtr,

        pub fn init(cache: CachePtr, end_address: Address) Self {
            return .{
                .cache = cache,
                .end_address = end_address,
            };
        }

        pub fn next(self: *Self) ?Address {
            var address = self.next_address orelse self.cache.freeHead();
            while (true) {
                if (address == InvalidAddr or
                    address >= self.cache.slotsLen() or
                    !isFree(self.cache, address))
                {
                    return null;
                }
                const next_address = nextFree(self.cache, address);
                self.next_address = next_address;
                if (address < self.end_address) {
                    return address;
                }
                address = next_address;
            }
        }
    };
}

// LinearPrefixFreeSlotsLocator scans the compact prefix linearly. It is better
// when the free-list is larger than the occupied part of storage: scanning the
// short prefix is cheaper and more cache-friendly than chasing many free links.
pub fn LinearPrefixFreeSlotsLocator(comptime CachePtr: type) type {
    return struct {
        const Self = @This();

        end_address: Address,
        current_address: Address = 0,
        cache: CachePtr,

        pub fn init(cache: CachePtr, end_address: Address) Self {
            return .{
                .cache = cache,
                .end_address = end_address,
            };
        }

        pub fn next(self: *Self) ?Address {
            while (self.current_address < self.end_address) {
                const address = self.current_address;
                self.current_address += 1;
                if (isFree(self.cache, address)) {
                    return address;
                }
            }
            return null;
        }
    };
}

// reclaim compacts occupied addresses into the beginning of storage and asks
// the concrete cache to release excess backing memory.
//
// If anchor is supplied and its node is moved during compaction, the returned
// address points to the node's new address. Tree-level code can pass the root
// address and then recompute min/max from the relocated root.
//
// loadFactor is a storage policy knob. It is clamped to 100 and describes how
// much free capacity may remain after compaction:
//
//                     new_free_count
//  loadFactor = ------------------------ * 100
//                 current_storage_length
//
// The concrete cache decides how retained slots map to physical memory. An
// ArrayList-backed cache may keep spare capacity, while a chunked cache may keep
// enough chunks for the occupied prefix plus new_free_count addresses.
pub fn reclaim(cache: anytype, loadFactor: u16, anchor: ?Address) ?Address {
    var new_anchor = anchor;
    const CachePtr = @TypeOf(cache);
    const actual_load_factor = @min(@as(usize, loadFactor), 100);
    if (cache.slotsLen() == 0) {
        cache.finishReclaim(0);
    } else {
        const new_free_count = (actual_load_factor * cache.slotsLen()) / 100;
        if (cache.freeCount() <= new_free_count) {
            return new_anchor;
        }
        const used_slots_count = cache.slotsLen() - cache.freeCount();
        const first_tail_address: Address = @intCast(used_slots_count);

        // Used slots in [used_slots_count..slotsLen) must be moved into free
        // holes in [0..used_slots_count), producing a compact used prefix.
        var usedLocator = UsedSlotsLocator(CachePtr).init(cache, first_tail_address);
        if (cache.freeCount() <= used_slots_count) {
            // If the free-list is relatively small, follow it directly. Free
            // slots outside the compact prefix are ignored because they will be
            // dropped from the logical storage length.
            var freeLocator = FreeListSlotsLocator(CachePtr).init(cache, first_tail_address);
            new_anchor = relocateStream(cache, &usedLocator, &freeLocator, new_anchor);
        } else {
            // If the free-list is larger than the occupied prefix, scanning the
            // short prefix linearly is usually cheaper and more cache-friendly
            // than chasing many free-list links through the tail.
            var freeLocator = LinearPrefixFreeSlotsLocator(CachePtr).init(cache, first_tail_address);
            new_anchor = relocateStream(cache, &usedLocator, &freeLocator, new_anchor);
        }
        cache.finishReclaim(new_free_count);
    }
    return new_anchor;
}

pub fn testReclaimEmpty(comptime LocationType: type) !void {
    const a = std.testing.allocator;
    var cache = try LocationType.init(a);
    defer cache.deinit();

    try std.testing.expectEqual(@as(?LocationType.Location, null), cache.reclaim(0, null));
}

pub fn testReclaimCompactsPrefix(comptime LocationType: type) !void {
    const a = std.testing.allocator;
    var cache = try LocationType.init(a);
    defer cache.deinit();

    var locs: [8]LocationType.Location = undefined;
    for (&locs, 0..) |*loc, idx| {
        loc.* = try cache.create();
        cache.data(loc.*).k = @intCast(idx);
        cache.data(loc.*).v = @intCast(idx);
    }

    cache.destroy(locs[1]);
    cache.destroy(locs[6]);
    cache.destroy(locs[3]);
    cache.destroy(locs[7]);

    const moved_anchor = cache.reclaim(25, locs[4]).?;

    try std.testing.expectEqual(@as(usize, 4), cache.slotsLen());
    try std.testing.expectEqual(@as(usize, 0), cache.freeCount());
    try std.testing.expectEqual(LocationType.InvalidAddr, cache.freeHead());

    for (0..cache.slotsLen()) |idx| {
        try std.testing.expect(cache.slotAt(@intCast(idx)).* == .used);
    }

    try std.testing.expectEqual(@as(LocationType.Address, 3), moved_anchor.addr);
    try std.testing.expectEqual(@as(i64, 4), cache.data(moved_anchor).k);
    try std.testing.expectEqual(@as(i64, 5), cache.slotAt(1).used.data.k);
}

pub fn testReclaimScansPrefixWhenFreeListIsLarger(comptime LocationType: type) !void {
    const a = std.testing.allocator;
    var cache = try LocationType.init(a);
    defer cache.deinit();

    var locs: [10]LocationType.Location = undefined;
    for (&locs, 0..) |*loc, idx| {
        loc.* = try cache.create();
        cache.data(loc.*).k = @intCast(idx);
        cache.data(loc.*).v = @intCast(idx);
    }

    cache.destroy(locs[0]);
    cache.destroy(locs[1]);
    cache.destroy(locs[2]);
    cache.destroy(locs[3]);
    cache.destroy(locs[5]);
    cache.destroy(locs[6]);
    cache.destroy(locs[7]);

    const moved_anchor = cache.reclaim(0, locs[8]).?;

    try std.testing.expectEqual(@as(usize, 3), cache.slotsLen());
    try std.testing.expectEqual(@as(usize, 0), cache.freeCount());
    try std.testing.expectEqual(LocationType.InvalidAddr, cache.freeHead());
    try std.testing.expectEqual(@as(LocationType.Address, 1), moved_anchor.addr);

    try std.testing.expectEqual(@as(i64, 4), cache.slotAt(0).used.data.k);
    try std.testing.expectEqual(@as(i64, 8), cache.slotAt(1).used.data.k);
    try std.testing.expectEqual(@as(i64, 9), cache.slotAt(2).used.data.k);
}

pub fn testReclaimClampsLoadFactor(comptime LocationType: type) !void {
    const a = std.testing.allocator;
    var cache = try LocationType.init(a);
    defer cache.deinit();

    const l1 = try cache.create();
    const l2 = try cache.create();
    cache.destroy(l1);

    try std.testing.expectEqual(l2, cache.reclaim(200, l2).?);
    try std.testing.expectEqual(@as(usize, 2), cache.slotsLen());
    try std.testing.expectEqual(@as(usize, 1), cache.freeCount());
}
