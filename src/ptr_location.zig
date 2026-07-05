const std = @import("std");
const direction = @import("direction.zig").direction;
const makeNodeType = @import("node.zig").MakeNodeType;
const utils = @import("utils.zig");

fn MakePtrLocationType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        const Node = makeNodeType(K, V, Self, Tags);
        const NodeData = Node.NodeData;

        ptr: *Node,

        fn init(ptr: *Node) Self {
            return Self{
                .ptr = ptr,
            };
        }

        pub fn eq(self: *const Self, other: Self) bool {
            return self.ptr == other.ptr;
        }

        pub fn data(self: *const Self) *NodeData {
            return &self.ptr.data;
        }

        pub fn child(self: *const Self, comptime dir: direction) ?Self {
            switch (dir) {
                .left => return self.ptr.*.left,
                .right => return self.ptr.*.right,
                else => unreachable,
            }
        }

        pub fn setChild(self: *Self, comptime dir: direction, loc: ?Self) void {
            switch (dir) {
                .left => self.ptr.*.left = loc,
                .right => self.ptr.*.right = loc,
                else => unreachable,
            }
        }

        pub fn parent(self: *const Self) ?Self {
            return self.ptr.*.parent;
        }

        pub fn setParent(self: *Self, p: ?Self) void {
            self.ptr.*.parent = p;
        }
    };
}

pub fn LocationCache(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        pub const Location = MakePtrLocationType(K, V, Tags);

        a: std.mem.Allocator,

        pub fn init(a: std.mem.Allocator) !Self {
            return Self{
                .a = a,
            };
        }

        pub fn deinit(_: *Self) void {}

        pub fn create(self: *Self) !Location {
            const node = try self.a.create(Location.Node);
            node.* = Location.Node.init();
            return Location.init(node);
        }

        pub fn destroy(self: *Self, loc: Location) void {
            self.a.destroy(loc.ptr);
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return utils.fastDeinitAllowed(self.a);
        }
    };
}
