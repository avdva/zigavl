const std = @import("std");
const direction = @import("direction.zig").direction;
const makeNodeType = @import("node.zig").MakeNodeType;
const ll = @import("linked_arraylist.zig");
const utils = @import("utils.zig");

fn MakeLLLocationType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        const Node = makeNodeType(K, V, Self, Tags);
        const NodeData = Node.NodeData;

        addr: ll.Address,
        list: *ll.LinkedArrayList(Node),

        fn init(addr: ll.Address, list: *ll.LinkedArrayList(Node)) Self {
            return Self{
                .addr = addr,
                .list = list,
            };
        }

        pub fn eq(self: *const Self, other: Self) bool {
            return self.addr == other.addr;
        }

        pub fn data(self: *const Self) *NodeData {
            return &self.list.*.getPtr(self.addr).*.data;
        }

        pub fn child(self: *const Self, comptime dir: direction) ?Self {
            const ptr = self.list.*.getPtr(self.addr);
            switch (dir) {
                .left => return ptr.*.left,
                .right => return ptr.*.right,
                else => unreachable,
            }
        }

        pub fn setChild(self: *Self, comptime dir: direction, loc: ?Self) void {
            const ptr = self.list.*.getPtr(self.addr);
            switch (dir) {
                .left => ptr.*.left = loc,
                .right => ptr.*.right = loc,
                else => unreachable,
            }
        }

        pub fn parent(self: *const Self) ?Self {
            const ptr = self.list.*.getPtr(self.addr);
            return ptr.*.parent;
        }

        pub fn setParent(self: *Self, p: ?Self) void {
            const ptr = self.list.*.getPtr(self.addr);
            ptr.*.parent = p;
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
            const node = try self.list.push(Location.Node.init());
            return Location.init(node, &self.list);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            _ = self.list.deleteAtAddr(loc.addr);
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }
    };
}
