const std = @import("std");
const direction = @import("direction.zig").direction;
const ll = @import("linked_arraylist.zig");
const makeNodeType = @import("node.zig").MakeNodeType;
const utils = @import("utils.zig");

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();

        pub const Location = struct {
            const Loc = @This();
            const Node = makeNodeType(K, V, Loc, Tags);
            const NodeData = Node.NodeData;

            addr: ll.Address,
            cache: *Self,

            fn init(addr: ll.Address, cache: *Self) Loc {
                return Loc{
                    .addr = addr,
                    .cache = cache,
                };
            }

            fn node(self: *const Loc) *Node {
                return &self.cache.nodes.items[self.addr].node;
            }

            pub fn eq(self: *const Loc, other: Loc) bool {
                return self.addr == other.addr;
            }

            pub fn data(self: *const Loc) *NodeData {
                return &self.node().data;
            }

            pub fn child(self: *const Loc, comptime dir: direction) ?Loc {
                switch (dir) {
                    .left => return self.node().left,
                    .right => return self.node().right,
                    else => unreachable,
                }
            }

            pub fn setChild(self: *Loc, comptime dir: direction, loc: ?Loc) void {
                switch (dir) {
                    .left => self.node().left = loc,
                    .right => self.node().right = loc,
                    else => unreachable,
                }
            }

            pub fn parent(self: *const Loc) ?Loc {
                return self.node().parent;
            }

            pub fn setParent(self: *Loc, p: ?Loc) void {
                self.node().parent = p;
            }
        };

        const Slot = struct {
            node: Location.Node,
            next_free: ll.Address = ll.InvalidAddr,
        };

        a: std.mem.Allocator,
        nodes: std.ArrayList(Slot),
        free_head: ll.Address,
        free_count: usize,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
                .nodes = try std.ArrayList(Slot).initCapacity(a, 16),
                .free_head = ll.InvalidAddr,
                .free_count = 0,
            };
        }

        pub fn deinit(self: *Self) void {
            self.nodes.deinit(self.a);
        }

        pub fn create(self: *Self) !Location {
            if (self.free_head != ll.InvalidAddr) {
                const addr = self.free_head;
                const slot = &self.nodes.items[addr];
                self.free_head = slot.next_free;
                self.free_count -= 1;
                slot.* = Slot{ .node = Location.Node.init() };
                return Location.init(addr, self);
            }

            const addr: ll.Address = @intCast(self.nodes.items.len);
            try self.nodes.append(self.a, Slot{ .node = Location.Node.init() });
            return Location.init(addr, self);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            const slot = &self.nodes.items[loc.addr];
            slot.next_free = self.free_head;
            self.free_head = loc.addr;
            self.free_count += 1;
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }
    };
}
