const std = @import("std");
const direction = @import("direction.zig").direction;
const node_lib = @import("node.zig");
const utils = @import("utils.zig");

fn MakePtrLocationType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        pub const NodeData = node_lib.makeDataType(K, V, Tags);

        const Node = struct {
            data: NodeData,
            left: ?Self,
            right: ?Self,
            parent: ?Self,

            fn init() Node {
                return Node{
                    .data = NodeData{},
                    .left = null,
                    .right = null,
                    .parent = null,
                };
            }
        };

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

        pub fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs.eq(rhs);
        }

        pub fn data(_: *Self, loc: Location) *Location.NodeData {
            return loc.data();
        }

        pub fn child(_: *Self, loc: Location, comptime dir: direction) ?Location {
            return loc.child(dir);
        }

        pub fn setChild(_: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            loc.setChild(dir, child_loc);
        }

        pub fn parent(_: *Self, loc: Location) ?Location {
            return loc.parent();
        }

        pub fn setParent(_: *Self, loc: *Location, p: ?Location) void {
            loc.setParent(p);
        }
    };
}
