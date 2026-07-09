const std = @import("std");
const direction = @import("direction.zig").direction;
const makeNodeType = @import("node.zig").MakeNodeType;
const ll = @import("linked_arraylist.zig");
const utils = @import("utils.zig");

fn MakeLLLocationType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        const Node = makeNodeType(K, V, Self, Tags);
        pub const NodeData = Node.NodeData;

        addr: ll.Address,

        fn init(addr: ll.Address) Self {
            return Self{
                .addr = addr,
            };
        }
    };
}

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        pub const Location = MakeLLLocationType(K, V, Tags);

        a: std.mem.Allocator,
        list: ll.LinkedArrayList(Location.Node),

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
                .list = try ll.LinkedArrayList(Location.Node).initOptions(a, .{}),
            };
        }

        pub fn deinit(self: *Self) void {
            self.list.deinit();
        }

        pub fn create(self: *Self) !Location {
            const addr = try self.list.push(Location.Node.init());
            return Location.init(addr);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            _ = self.list.deleteAtAddr(loc.addr);
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }

        fn node(self: *Self, loc: Location) *Location.Node {
            return self.list.getPtr(loc.addr);
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
