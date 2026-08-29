const std = @import("std");
const address_storage = @import("address_storage.zig");
const cache_contract = @import("cache_contract.zig");
const direction = @import("direction.zig").direction;
const utils = @import("utils.zig");

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
            return utils.fastDeinitAllowed(self.a);
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
    };
}
