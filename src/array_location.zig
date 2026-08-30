const std = @import("std");
const address_storage = @import("address_storage.zig");
const cache_contract = @import("cache_contract.zig");
const direction = @import("direction.zig").direction;
const node_lib = @import("node.zig");
const utils = @import("utils.zig");

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        pub const Address = address_storage.Address;
        pub const InvalidAddr = address_storage.InvalidAddr;
        const NodeData = node_lib.MakeDataType(K, V, Tags);

        // Location is a compact handle into the cache's slots array.
        // It deliberately does not store a pointer back to the cache; all storage
        // access goes through LocationCache methods.
        // The handle stays valid across ArrayList reallocations, but pointers
        // returned to node values can be invalidated by future insertions.
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
        pub const Meta = cache_contract.Meta(Tags);

        a: std.mem.Allocator,
        nodes: std.ArrayList(Slot),
        free_head: Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
                .nodes = try std.ArrayList(Slot).initCapacity(a, 16),
                .free_head = InvalidAddr,
                .free_count = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.nodes.deinit(self.a);
        }

        pub fn clearAll(self: *Self) void {
            self.nodes.deinit(self.a);
            self.nodes = .empty;
            self.free_head = InvalidAddr;
            self.free_count = 0;
        }

        pub fn create(self: *Self) !Location {
            if (self.free_head != InvalidAddr) {
                const addr = self.free_head;
                const slot = &self.nodes.items[addr];
                self.free_head = slot.free;
                self.free_count -= 1;
                slot.* = Slot{ .used = Node.init() };
                return Location.init(addr);
            }

            const addr: Address = @intCast(self.nodes.items.len);
            try self.nodes.append(self.a, Slot{ .used = Node.init() });
            return Location.init(addr);
        }

        // destroy only returns the slot to this cache's free-list. The backing
        // ArrayList is not shrunk here, so memory usage can grow with the peak
        // number of nodes and is released only by deinit().
        pub fn destroy(self: *Self, loc: Location) void {
            self.destroyAtAddress(loc.addr);
        }

        fn destroyAtAddress(self: *Self, addr: Address) void {
            self.nodes.items[addr] = Slot{ .free = self.free_head };
            self.free_head = addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }

        fn node(self: *Self, loc: Location) *Node {
            return &self.nodes.items[loc.addr].used;
        }

        pub fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.addr == rhs.addr;
        }

        pub fn keyPtr(self: *Self, loc: Location) *K {
            return &self.node(loc).data.k;
        }

        pub fn valuePtr(self: *Self, loc: Location) *V {
            return &self.node(loc).data.v;
        }

        pub fn meta(self: *Self, loc: Location) Meta {
            const data_ptr = &self.node(loc).data;
            return .{
                .height = &data_ptr.h,
                .tags = &data_ptr.tags,
            };
        }

        pub fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            const addr = switch (dir) {
                .left => self.node(loc).left,
                .right => self.node(loc).right,
                else => unreachable,
            };
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            const addr = if (child_loc) |child_loc_val| child_loc_val.addr else InvalidAddr;
            switch (dir) {
                .left => self.node(loc.*).left = addr,
                .right => self.node(loc.*).right = addr,
                else => unreachable,
            }
        }

        pub fn parent(self: *Self, loc: Location) ?Location {
            const addr = self.node(loc).parent;
            return if (addr == InvalidAddr) null else Location.init(addr);
        }

        pub fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.node(loc.*).parent = if (p) |parent_loc| parent_loc.addr else InvalidAddr;
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
            return self.nodes.items.len;
        }

        pub fn freeCount(self: *Self) usize {
            return self.free_count;
        }

        pub fn freeHead(self: *Self) Address {
            return self.free_head;
        }

        pub fn slotAt(self: *Self, addr: Address) *Slot {
            return &self.nodes.items[addr];
        }

        // finishReclaim finalizes address compaction for ArrayList-backed
        // storage. The shared compaction code has already moved occupied slots
        // into the retained prefix; this method shrinks allocation according to
        // new_free_count, trims the logical length to used slots, and clears the
        // free-list metadata because reclaimed free slots no longer exist.
        pub fn finishReclaim(self: *Self, new_free_count: usize) void {
            const used_count = self.nodes.items.len - self.free_count;
            if (used_count == 0 and self.nodes.items.len == 0 and self.nodes.capacity > 0) {
                self.nodes.expandToCapacity();
            }
            self.nodes.shrinkAndFree(self.a, used_count + new_free_count);
            self.nodes.shrinkRetainingCapacity(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }

        // finishOrderStorage trims the logical slot list to the occupied prefix
        // after every live node has been moved into sorted address order. Free
        // slots are gone, but retained capacity can still be reused by append().
        pub fn finishOrderStorage(self: *Self, used_count: usize) void {
            self.nodes.shrinkRetainingCapacity(used_count);
            self.free_count = 0;
            self.free_head = InvalidAddr;
        }
    };
}

test "locationcache reclaim" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimEmpty(LocationType);
}

test "locationcache reclaim compacts prefix" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimCompactsPrefix(LocationType);
}

test "locationcache reclaim scans prefix when free list is larger than used part" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimScansPrefixWhenFreeListIsLarger(LocationType);
}

test "locationcache reclaim clamps load factor" {
    const LocationType = LocationCache(i64, i64, struct {});
    try address_storage.testReclaimClampsLoadFactor(LocationType);
}

test "locationcache reclaim preserves spare capacity" {
    const a = std.testing.allocator;
    const LocationType = LocationCache(i64, i64, struct {});
    var lc = try LocationType.init(a);
    defer lc.deinit();

    const l1 = try lc.create();
    const l2 = try lc.create();
    lc.destroy(l1);
    const capacity_before = lc.nodes.capacity;

    try std.testing.expectEqual(l2, lc.reclaim(200, l2).?);
    try std.testing.expectEqual(capacity_before, lc.nodes.capacity);
}
