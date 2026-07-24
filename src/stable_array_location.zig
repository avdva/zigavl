const std = @import("std");
const direction = @import("direction.zig").direction;
const node_lib = @import("node.zig");
const utils = @import("utils.zig");

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        const Address = u32;
        const InvalidAddr = std.math.maxInt(Address);

        // Location is a compact stable handle into this cache.
        // It stores only a logical address, so tree nodes can refer to each other
        // without embedding pointers. Storage access always goes through the cache.
        pub const Location = struct {
            const Loc = @This();
            pub const NodeData = node_lib.MakeDataType(K, V, Tags);

            addr: Address,

            fn init(addr: Address) Loc {
                return Loc{
                    .addr = addr,
                };
            }
        };

        const Node = struct {
            data: Location.NodeData,
            left: Address,
            right: Address,
            parent: Address,

            fn init() Node {
                return Node{
                    .data = Location.NodeData{},
                    .left = InvalidAddr,
                    .right = InvalidAddr,
                    .parent = InvalidAddr,
                };
            }
        };

        // A slot is either occupied by a tree node or belongs to the free-list.
        // Free slots store the next free address directly, with InvalidAddr as
        // the end-of-list sentinel. No tagged state is stored separately.
        const Slot = union {
            used: Node,
            free: Address,
        };

        const chunk_bits = 10;
        const chunk_len = 1 << chunk_bits;
        const chunk_mask = chunk_len - 1;

        const Chunk = struct {
            slots: [chunk_len]Slot = undefined,
        };

        a: std.mem.Allocator,
        chunks: std.ArrayList(*Chunk),
        len: Address,
        free_head: Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
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
            self.slot(loc.addr).* = Slot{ .free = self.free_head };
            self.free_head = loc.addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
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

        pub inline fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.addr == rhs.addr;
        }

        pub inline fn data(self: *Self, loc: Location) *Location.NodeData {
            return &self.slot(loc.addr).used.data;
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
    };
}
