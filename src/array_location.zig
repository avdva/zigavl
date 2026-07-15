const std = @import("std");
const direction = @import("direction.zig").direction;
const node_lib = @import("node.zig");
const utils = @import("utils.zig");

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        const Address = u32;
        const InvalidAddr = std.math.maxInt(Address);

        // Location is a compact stable handle into the cache's slots array.
        // It deliberately does not store a pointer back to the cache; all storage
        // access goes through LocationCache methods.
        pub const Location = struct {
            const Loc = @This();
            pub const NodeData = node_lib.makeDataType(K, V, Tags);

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
            self.nodes.items[loc.addr] = Slot{ .free = self.free_head };
            self.free_head = loc.addr;
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

        pub fn data(self: *Self, loc: Location) *Location.NodeData {
            return &self.node(loc).data;
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
    };
}
