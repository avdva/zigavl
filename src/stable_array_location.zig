const std = @import("std");
const address_storage = @import("address_storage.zig");
const cache_contract = @import("cache_contract.zig");
const direction = @import("direction.zig").direction;

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        pub const Address = address_storage.Address;
        pub const InvalidAddr = address_storage.InvalidAddr;
        const NodeData = struct {
            k: K = undefined,
            v: V = undefined,
            tags: Tags = undefined,
            h: u8 = 0,
        };

        // Location is a compact stable handle into this cache.
        // It stores only a logical address, so tree nodes can refer to each other
        // without embedding pointers. Storage access always goes through the cache.
        pub const Location = struct {
            const Loc = @This();

            addr: Address,

            fn init(addr: Address) Loc {
                return Loc{
                    .addr = addr,
                };
            }
        };

        const Node = struct {
            data: NodeData,
            left: Address,
            right: Address,
            parent: Address,

            fn init() Node {
                return Node{
                    .data = NodeData{},
                    .left = InvalidAddr,
                    .right = InvalidAddr,
                    .parent = InvalidAddr,
                };
            }
        };

        const Slot = address_storage.MakeSlot(Node);

        const chunk_bits = 10;
        const chunk_len = 1 << chunk_bits;
        const chunk_mask = chunk_len - 1;

        const Chunk = struct {
            slots: [chunk_len]Slot = undefined,
        };

        a: std.mem.Allocator,
        fast_deinit_allowed: bool,
        chunks: std.ArrayList(*Chunk),
        len: Address,
        free_head: Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
                .fast_deinit_allowed = cache_contract.fastDeinitAllowed(a),
                .chunks = try std.ArrayList(*Chunk).initCapacity(a, 1),
                .len = 0,
                .free_head = InvalidAddr,
                .free_count = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            for (self.chunks.items) |chunk| {
                self.a.destroy(chunk);
            }
            self.chunks.deinit(self.a);
        }

        pub fn clearAll(self: *Self) void {
            for (self.chunks.items) |chunk| {
                self.a.destroy(chunk);
            }
            self.chunks.deinit(self.a);
            self.chunks = .empty;
            self.len = 0;
            self.free_head = InvalidAddr;
            self.free_count = 0;
        }

        pub fn create(self: *Self) !Location {
            if (self.free_head != InvalidAddr) {
                const addr = self.free_head;
                const free_slot = self.slot(addr);
                self.free_head = free_slot.free;
                self.free_count -= 1;
                free_slot.* = Slot{ .used = Node.init() };
                return Location.init(addr);
            }

            if (self.len == InvalidAddr) {
                return error.OutOfMemory;
            }
            if (@as(usize, self.len) == self.chunks.items.len * chunk_len) {
                const chunk = try self.a.create(Chunk);
                try self.chunks.append(self.a, chunk);
            }

            const addr = self.len;
            self.len += 1;
            self.slot(addr).* = Slot{ .used = Node.init() };
            return Location.init(addr);
        }

        // destroy only returns the slot to this cache's free-list. Chunks are
        // not freed here, so memory usage can grow with the peak number of nodes
        // and is released only by deinit().
        pub fn destroy(self: *Self, loc: Location) void {
            self.destroyAtAddress(loc.addr);
        }

        fn destroyAtAddress(self: *Self, addr: Address) void {
            self.slot(addr).* = Slot{ .free = self.free_head };
            self.free_head = addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return self.fast_deinit_allowed;
        }

        inline fn chunkIndex(addr: Address) usize {
            return @as(usize, addr >> chunk_bits);
        }

        inline fn slotIndex(addr: Address) usize {
            return @as(usize, addr & chunk_mask);
        }

        inline fn slot(self: *Self, addr: Address) *Slot {
            return &self.chunks.items[chunkIndex(addr)].slots[slotIndex(addr)];
        }

        pub inline fn slotAt(self: *Self, addr: Address) *Slot {
            return self.slot(addr);
        }

        pub fn swapSlots(self: *Self, addr_1: Address, addr_2: Address) void {
            std.mem.swap(Slot, self.slotAt(addr_1), self.slotAt(addr_2));
        }

        pub inline fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.addr == rhs.addr;
        }

        pub inline fn keyPtr(self: *Self, loc: Location) *K {
            return &self.slot(loc.addr).used.data.k;
        }

        pub inline fn valuePtr(self: *Self, loc: Location) *V {
            return &self.slot(loc.addr).used.data.v;
        }

        pub inline fn meta(self: *Self, loc: Location) cache_contract.Meta(Tags) {
            const data_ptr = &self.slot(loc.addr).used.data;
            return .{
                .height = &data_ptr.h,
                .tags = &data_ptr.tags,
            };
        }

        pub inline fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            const addr = switch (dir) {
                .left => self.slot(loc.addr).used.left,
                .right => self.slot(loc.addr).used.right,
                else => unreachable,
            };
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub inline fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            const addr = if (child_loc) |child_loc_val| child_loc_val.addr else InvalidAddr;
            switch (dir) {
                .left => self.slot(loc.addr).used.left = addr,
                .right => self.slot(loc.addr).used.right = addr,
                else => unreachable,
            }
        }

        pub inline fn parent(self: *Self, loc: Location) ?Location {
            const addr = self.slot(loc.addr).used.parent;
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub inline fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.slot(loc.addr).used.parent = if (p) |parent_loc| parent_loc.addr else InvalidAddr;
        }

        // reclaim delegates address compaction to the shared storage logic and
        // converts the returned anchor address back to Location.
        pub fn reclaim(self: *Self, loadFactor: u16, anchor: ?Location) ?Location {
            const anchor_addr = if (anchor) |loc| loc.addr else null;
            const new_anchor = address_storage.reclaim(self, loadFactor, anchor_addr);
            return if (new_anchor) |addr| Location.init(addr) else null;
        }

        // relocate moves the occupied slot addressed by loc to address pos,
        // updating all address links touched by the move. It returns the new
        // Location of that same node.
        pub fn relocate(self: *Self, loc: Location, pos: usize) Location {
            return Location.init(address_storage.relocate(self, loc.addr, @intCast(pos)));
        }

        // locationAt converts a storage address to a Location handle. Callers are
        // responsible for only passing addresses known to contain occupied slots.
        pub fn locationAt(_: *Self, pos: usize) Location {
            return Location.init(@intCast(pos));
        }

        // nextLocation returns the handle for the next storage slot when the
        // caller treats a dense slot range as an ordered sequence.
        pub fn nextLocation(_: *Self, loc: Location, len: usize) ?Location {
            const next_addr = loc.addr + 1;
            return if (next_addr < len) Location.init(next_addr) else null;
        }

        // prevLocation returns the handle for the previous storage slot when the
        // caller treats a dense slot range as an ordered sequence.
        pub fn prevLocation(_: *Self, loc: Location) ?Location {
            return if (loc.addr > 0) Location.init(loc.addr - 1) else null;
        }

        pub fn slotsLen(self: *Self) usize {
            return self.len;
        }

        pub fn freeCount(self: *Self) usize {
            return self.free_count;
        }

        pub fn freeHead(self: *Self) Address {
            return self.free_head;
        }

        // finishReclaim finalizes address compaction for chunk-backed storage.
        // The shared compaction code has already moved occupied slots into the
        // retained prefix; this method computes how many chunks are still needed,
        // releases tail chunks, trims the logical length to used slots, and clears
        // the free-list metadata because reclaimed free slots no longer exist.
        pub fn finishReclaim(self: *Self, new_free_count: usize) void {
            const used_count = @as(usize, self.len) - self.free_count;
            const retained_slots = used_count + new_free_count;
            const retained_chunks = if (retained_slots == 0)
                0
            else
                std.math.divCeil(usize, retained_slots, chunk_len) catch unreachable;

            for (self.chunks.items[retained_chunks..]) |chunk| {
                self.a.destroy(chunk);
            }
            self.chunks.shrinkAndFree(self.a, retained_chunks);
            self.len = @intCast(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }

        // finishOrderStorage trims the logical storage length to the occupied
        // prefix after every live node has been moved into sorted address order.
        // Existing chunks are retained for future insertions.
        pub fn finishOrderStorage(self: *Self, used_count: usize) void {
            self.len = @intCast(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }
    };
}

test "stable locationcache reclaim" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimEmpty(LocationType);
}

test "stable locationcache reclaim compacts prefix" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimCompactsPrefix(LocationType);
}

test "stable locationcache reclaim scans prefix when free list is larger than used part" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimScansPrefixWhenFreeListIsLarger(LocationType);
}

test "stable locationcache reclaim clamps load factor" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimClampsLoadFactor(LocationType);
}

test "stable locationcache reclaim frees tail chunks" {
    const a = std.testing.allocator;
    const LocationType = LocationCache(i64, i64, struct {});
    var lc = try LocationType.init(a);
    defer lc.deinit();

    var locs: [1100]LocationType.Location = undefined;
    for (&locs, 0..) |*loc, idx| {
        loc.* = try lc.create();
        lc.keyPtr(loc.*).* = @intCast(idx);
        lc.valuePtr(loc.*).* = @intCast(idx);
    }

    for (0..locs.len - 1) |idx| {
        if (idx == 500) {
            continue;
        }
        lc.destroy(locs[idx]);
    }

    const moved_anchor = lc.reclaim(0, locs[locs.len - 1]).?;

    try std.testing.expectEqual(@as(LocationType.Address, 2), lc.len);
    try std.testing.expectEqual(@as(usize, 1), lc.chunks.items.len);
    try std.testing.expectEqual(@as(usize, 0), lc.free_count);
    try std.testing.expectEqual(LocationType.InvalidAddr, lc.free_head);
    try std.testing.expectEqual(@as(u32, 1), moved_anchor.addr);
    try std.testing.expectEqual(@as(i64, 500), lc.slot(0).used.data.k);
    try std.testing.expectEqual(@as(i64, @intCast(locs.len - 1)), lc.slot(1).used.data.k);
}
