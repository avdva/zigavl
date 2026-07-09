const std = @import("std");
const address = @import("address.zig");
const direction = @import("direction.zig").direction;
const makeNodeType = @import("node.zig").MakeNodeType;
const utils = @import("utils.zig");

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        pub const Location = struct {
            const Loc = @This();
            const Node = makeNodeType(K, V, Loc, Tags);
            pub const NodeData = Node.NodeData;

            addr: address.Address,

            fn init(addr: address.Address) Loc {
                return Loc{
                    .addr = addr,
                };
            }
        };

        const Slot = union {
            used: Location.Node,
            free: address.Address,
        };

        a: std.mem.Allocator,
        nodes: std.ArrayList(Slot),
        free_head: address.Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
                .nodes = try std.ArrayList(Slot).initCapacity(a, 16),
                .free_head = address.InvalidAddr,
                .free_count = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.nodes.deinit(self.a);
        }

        pub fn create(self: *Self) !Location {
            if (self.free_head != address.InvalidAddr) {
                const addr = self.free_head;
                const slot = &self.nodes.items[addr];
                self.free_head = slot.free;
                self.free_count -= 1;
                slot.* = Slot{ .used = Location.Node.init() };
                return Location.init(addr);
            }

            const addr: address.Address = @intCast(self.nodes.items.len);
            try self.nodes.append(self.a, Slot{ .used = Location.Node.init() });
            return Location.init(addr);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            self.nodes.items[loc.addr] = Slot{ .free = self.free_head };
            self.free_head = loc.addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }

        fn node(self: *Self, loc: Location) *Location.Node {
            return &self.nodes.items[loc.addr].used;
        }

        pub fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.addr == rhs.addr;
        }

        pub fn data(self: *Self, loc: Location) *Location.NodeData {
            return &self.node(loc).data;
        }

        pub fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            switch (dir) {
                .left => return self.node(loc).left,
                .right => return self.node(loc).right,
                else => unreachable,
            }
        }

        pub fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            switch (dir) {
                .left => self.node(loc.*).left = child_loc,
                .right => self.node(loc.*).right = child_loc,
                else => unreachable,
            }
        }

        pub fn parent(self: *Self, loc: Location) ?Location {
            return self.node(loc).parent;
        }

        pub fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.node(loc.*).parent = p;
        }
    };
}
