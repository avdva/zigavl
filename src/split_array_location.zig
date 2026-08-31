const std = @import("std");
const address_storage = @import("address_storage.zig");
const cache_contract = @import("cache_contract.zig");
const direction = @import("direction.zig").direction;

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        pub const Address = address_storage.Address;
        pub const InvalidAddr = address_storage.InvalidAddr;

        pub const Location = struct {
            const Loc = @This();

            addr: Address,

            fn init(addr: Address) Loc {
                return .{ .addr = addr };
            }
        };

        pub const Meta = cache_contract.Meta(Tags);

        const Links = struct {
            left: Address = InvalidAddr,
            right: Address = InvalidAddr,
            parent: Address = InvalidAddr,
        };

        // The links array also owns the free-list state. A live slot stores tree
        // links; a destroyed slot stores the next free address. Keeping this tag
        // here avoids a separate slots array while preserving O(1) reuse.
        const LinkSlot = union(enum) {
            used: Links,
            free: Address,
        };

        const MetaStorage = struct {
            height: u8 = 0,
            tags: Tags = undefined,
        };

        a: std.mem.Allocator,
        fast_deinit_allowed: bool,

        // Split storage keeps frequently compared keys and navigation links away
        // from values. That lets search/rotation-heavy paths touch less unrelated
        // memory than a single array of full node structs.
        keys: std.ArrayList(K),
        values: std.ArrayList(V),
        metas: std.ArrayList(MetaStorage),
        links: std.ArrayList(LinkSlot),

        // Freed addresses are retained in a singly linked list threaded through
        // LinkSlot.free. The arrays only grow until deinit(); destroy() makes a
        // slot reusable but does not shrink backing allocations.
        free_head: Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return .{
                .a = a,
                .fast_deinit_allowed = cache_contract.fastDeinitAllowed(a),
                .keys = try std.ArrayList(K).initCapacity(a, 16),
                .values = try std.ArrayList(V).initCapacity(a, 16),
                .metas = try std.ArrayList(MetaStorage).initCapacity(a, 16),
                .links = try std.ArrayList(LinkSlot).initCapacity(a, 16),
                .free_head = InvalidAddr,
                .free_count = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.keys.deinit(self.a);
            self.values.deinit(self.a);
            self.metas.deinit(self.a);
            self.links.deinit(self.a);
        }

        pub fn clearAll(self: *Self) void {
            self.keys.deinit(self.a);
            self.values.deinit(self.a);
            self.metas.deinit(self.a);
            self.links.deinit(self.a);
            self.keys = .empty;
            self.values = .empty;
            self.metas = .empty;
            self.links = .empty;
            self.free_head = InvalidAddr;
            self.free_count = 0;
        }

        pub fn create(self: *Self) !Location {
            if (self.free_head != InvalidAddr) {
                const addr = self.free_head;
                self.free_head = self.links.items[addr].free;
                self.free_count -= 1;
                self.links.items[addr] = .{ .used = .{} };
                self.metas.items[addr] = .{};
                return Location.init(addr);
            }

            // All arrays must grow together because Location is a shared address
            // into keys, values, metadata, and links.
            const new_len = self.links.items.len + 1;
            try self.keys.ensureTotalCapacity(self.a, new_len);
            try self.values.ensureTotalCapacity(self.a, new_len);
            try self.metas.ensureTotalCapacity(self.a, new_len);
            try self.links.ensureTotalCapacity(self.a, new_len);

            const addr: Address = @intCast(self.links.items.len);
            self.keys.appendAssumeCapacity(undefined);
            self.values.appendAssumeCapacity(undefined);
            self.metas.appendAssumeCapacity(.{});
            self.links.appendAssumeCapacity(.{ .used = .{} });
            return Location.init(addr);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            self.links.items[loc.addr] = .{ .free = self.free_head };
            self.free_head = loc.addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return self.fast_deinit_allowed;
        }

        pub fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.addr == rhs.addr;
        }

        pub fn keyPtr(self: *Self, loc: Location) *K {
            return &self.keys.items[loc.addr];
        }

        pub fn valuePtr(self: *Self, loc: Location) *V {
            return &self.values.items[loc.addr];
        }

        pub fn meta(self: *Self, loc: Location) Meta {
            const meta_ptr = &self.metas.items[loc.addr];
            return .{
                .height = &meta_ptr.height,
                .tags = &meta_ptr.tags,
            };
        }

        fn linkPtr(self: *Self, loc: Location) *Links {
            return &self.links.items[loc.addr].used;
        }

        pub fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            const addr = switch (dir) {
                .left => self.linkPtr(loc).left,
                .right => self.linkPtr(loc).right,
                else => unreachable,
            };
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            const addr = if (child_loc) |child_loc_val| child_loc_val.addr else InvalidAddr;
            switch (dir) {
                .left => self.linkPtr(loc.*).left = addr,
                .right => self.linkPtr(loc.*).right = addr,
                else => unreachable,
            }
        }

        pub fn parent(self: *Self, loc: Location) ?Location {
            const addr = self.linkPtr(loc).parent;
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.linkPtr(loc.*).parent = if (p) |parent_loc| parent_loc.addr else InvalidAddr;
        }

        // reclaim delegates address compaction to the shared storage logic and
        // converts the returned anchor address back to Location.
        pub fn reclaim(self: *Self, loadFactor: u16, anchor: ?Location) ?Location {
            const anchor_addr = if (anchor) |loc| loc.addr else null;
            const new_anchor = address_storage.reclaim(self, loadFactor, anchor_addr);
            return if (new_anchor) |addr| Location.init(addr) else null;
        }

        // relocate moves the occupied element addressed by loc to address pos,
        // updating all address links touched by the move. It returns the new
        // Location of that same element.
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
            return self.links.items.len;
        }

        pub fn freeCount(self: *Self) usize {
            return self.free_count;
        }

        pub fn freeHead(self: *Self) Address {
            return self.free_head;
        }

        pub fn slotAt(self: *Self, addr: Address) *LinkSlot {
            return &self.links.items[addr];
        }

        // swapSlots keeps all split arrays aligned while moving an address slot.
        // The links/free-list tag is the authoritative occupancy state, but keys,
        // values, and metadata must move with live slots so each address continues
        // to describe one logical tree node.
        pub fn swapSlots(self: *Self, addr_1: Address, addr_2: Address) void {
            std.mem.swap(K, &self.keys.items[addr_1], &self.keys.items[addr_2]);
            std.mem.swap(V, &self.values.items[addr_1], &self.values.items[addr_2]);
            std.mem.swap(MetaStorage, &self.metas.items[addr_1], &self.metas.items[addr_2]);
            std.mem.swap(LinkSlot, self.slotAt(addr_1), self.slotAt(addr_2));
        }

        // finishReclaim finalizes address compaction for split ArrayList-backed
        // storage. The shared compaction code has already moved occupied slots
        // into the retained prefix; this method shrinks every parallel array in
        // lockstep and clears the free-list metadata.
        pub fn finishReclaim(self: *Self, new_free_count: usize) void {
            const used_count = self.links.items.len - self.free_count;
            if (used_count == 0 and self.links.items.len == 0 and self.links.capacity > 0) {
                self.keys.expandToCapacity();
                self.values.expandToCapacity();
                self.metas.expandToCapacity();
                self.links.expandToCapacity();
            }
            self.keys.shrinkAndFree(self.a, used_count + new_free_count);
            self.values.shrinkAndFree(self.a, used_count + new_free_count);
            self.metas.shrinkAndFree(self.a, used_count + new_free_count);
            self.links.shrinkAndFree(self.a, used_count + new_free_count);
            self.keys.shrinkRetainingCapacity(used_count);
            self.values.shrinkRetainingCapacity(used_count);
            self.metas.shrinkRetainingCapacity(used_count);
            self.links.shrinkRetainingCapacity(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }

        // finishOrderStorage trims every parallel array to the occupied prefix
        // after all live nodes have been moved into sorted address order. Free
        // slots are gone, but retained capacity can still be reused by append().
        pub fn finishOrderStorage(self: *Self, used_count: usize) void {
            self.keys.shrinkRetainingCapacity(used_count);
            self.values.shrinkRetainingCapacity(used_count);
            self.metas.shrinkRetainingCapacity(used_count);
            self.links.shrinkRetainingCapacity(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }
    };
}

test "split locationcache reclaim" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimEmpty(LocationType);
}

test "split locationcache reclaim compacts prefix" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimCompactsPrefix(LocationType);
}

test "split locationcache reclaim scans prefix when free list is larger than used part" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimScansPrefixWhenFreeListIsLarger(LocationType);
}

test "split locationcache reclaim clamps load factor" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimClampsLoadFactor(LocationType);
}
