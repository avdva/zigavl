const std = @import("std");
const direction = @import("direction.zig").direction;

pub fn Meta(comptime Tags: type) type {
    return struct {
        // AVL balance factor: right subtree height minus left subtree height.
        balance: *i8,
        tags: *Tags,
    };
}

// MakeLocationListSequentialBuilder creates a bulk-build session for caches
// whose locations cannot be reconstructed from an integer storage position.
// The location list is allocated before the old tree is cleared, so an
// allocation failure leaves the old tree intact.
pub fn MakeLocationListSequentialBuilder(comptime Cache: type) type {
    return struct {
        const Self = @This();
        const Location = Cache.Location;

        cache: *Cache,
        allocator: std.mem.Allocator,
        locations: []Location,
        created: usize = 0,
        committed: bool = false,

        pub fn init(cache: *Cache, allocator: std.mem.Allocator, count: usize) !Self {
            return .{
                .cache = cache,
                .allocator = allocator,
                .locations = try allocator.alloc(Location, count),
            };
        }

        pub fn prepare(_: *Self) !void {}

        pub fn append(self: *Self) !Location {
            std.debug.assert(self.created < self.locations.len);
            const loc = try self.cache.create();
            self.locations[self.created] = loc;
            self.created += 1;
            return loc;
        }

        pub fn locationAt(self: *Self, index: usize) Location {
            std.debug.assert(index < self.created);
            return self.locations[index];
        }

        pub fn commit(self: *Self) void {
            std.debug.assert(self.created == self.locations.len);
            self.committed = true;
        }

        pub fn deinit(self: *Self) void {
            if (!self.committed) {
                while (self.created > 0) {
                    self.created -= 1;
                    self.cache.destroy(self.locations[self.created]);
                }
            }
            self.allocator.free(self.locations);
        }
    };
}

// MakeIndexedSequentialBuilder creates a bulk-build session for caches whose
// freshly cleared storage assigns sequentially appended nodes to dense integer
// positions. It expects each cache.create() call to return a location equivalent
// to cache.locationAt(0), cache.locationAt(1), and so on. A cache that violates
// this contract causes append() to return error.InvalidSequentialLocation.
// No temporary location list is needed.
pub fn MakeIndexedSequentialBuilder(comptime Cache: type) type {
    return struct {
        const Self = @This();
        const Location = Cache.Location;

        cache: *Cache,
        count: usize,
        created: usize = 0,
        committed: bool = false,

        pub fn init(cache: *Cache, count: usize) Self {
            return .{
                .cache = cache,
                .count = count,
            };
        }

        pub fn prepare(self: *Self) !void {
            try self.cache.reserveNodes(self.count);
        }

        pub fn append(self: *Self) !Location {
            std.debug.assert(self.created < self.count);
            const loc = try self.cache.create();
            if (!self.cache.eq(loc, self.cache.locationAt(self.created))) {
                self.cache.destroy(loc);
                return error.InvalidSequentialLocation;
            }
            self.created += 1;
            return loc;
        }

        pub fn locationAt(self: *Self, index: usize) Location {
            std.debug.assert(index < self.created);
            return self.cache.locationAt(index);
        }

        pub fn commit(self: *Self) void {
            std.debug.assert(self.created == self.count);
            self.committed = true;
        }

        pub fn deinit(self: *Self) void {
            if (self.committed) return;
            while (self.created > 0) {
                self.created -= 1;
                self.cache.destroy(self.cache.locationAt(self.created));
            }
        }
    };
}

fn requireDecl(comptime Cache: type, comptime name: []const u8) void {
    if (!@hasDecl(Cache, name)) {
        @compileError("cache must declare " ++ name);
    }
}

fn requireFn(comptime Fn: type, comptime name: []const u8) std.builtin.Type.Fn {
    const info = @typeInfo(Fn);
    if (info != .@"fn") {
        @compileError("cache." ++ name ++ " must be a function");
    }
    return info.@"fn";
}

fn requireErrorUnionMethod(
    comptime Fn: type,
    comptime name: []const u8,
    comptime Params: []const type,
    comptime ExpectedPayload: type,
) void {
    const info = requireFn(Fn, name);
    if (info.params.len != Params.len) {
        @compileError("cache." ++ name ++ " has an unexpected parameter count");
    }
    inline for (Params, 0..) |Param, index| {
        requireParam(info.params, name, index, Param);
    }
    if (info.return_type == null) {
        @compileError("cache." ++ name ++ " must return an error union");
    }
    const return_type = info.return_type.?;
    const return_info = @typeInfo(return_type);
    if (return_info != .error_union or return_info.error_union.payload != ExpectedPayload) {
        @compileError("cache." ++ name ++ " has an unexpected error-union payload");
    }
}

fn requireParam(comptime params: []const std.builtin.Type.Fn.Param, comptime name: []const u8, comptime index: usize, comptime Expected: type) void {
    if (params[index].type == null or params[index].type.? != Expected) {
        @compileError("cache." ++ name ++ " has an unexpected parameter type");
    }
}

fn requireMethod(
    comptime Fn: type,
    comptime name: []const u8,
    comptime Params: []const type,
    comptime Return: type,
) void {
    const info = requireFn(Fn, name);
    if (info.params.len != Params.len) {
        @compileError("cache." ++ name ++ " has an unexpected parameter count");
    }
    inline for (Params, 0..) |Param, index| {
        requireParam(info.params, name, index, Param);
    }
    if (info.return_type == null or info.return_type.? != Return) {
        @compileError("cache." ++ name ++ " has an unexpected return type");
    }
}

fn requireDirMethod(
    comptime Fn: type,
    comptime name: []const u8,
    comptime Params: []const type,
    comptime Return: type,
) void {
    const info = requireFn(Fn, name);
    if (info.params.len != Params.len) {
        @compileError("cache." ++ name ++ " has an unexpected parameter count");
    }
    inline for (Params, 0..) |Param, index| {
        requireParam(info.params, name, index, Param);
    }
    if (info.return_type == null or info.return_type.? != Return) {
        @compileError("cache." ++ name ++ " has an unexpected return type");
    }
}

// assertBaseRequirements verifies the mandatory cache contract used by Tree.
// A cache type must provide:
//  - Location: an opaque handle identifying one stored node.
//  - init(allocator) and deinit(): create and release cache-owned storage.
//  - create() and destroy(loc): allocate/reclaim one node slot.
//  - fastDeinitAllowed(): report whether deinit can skip per-node destruction.
//  - eq(lhs, rhs): compare two Location handles.
//  - keyPtr(loc) and valuePtr(loc): access stored key/value fields.
//  - meta(loc): return cache_contract.Meta(Tags) for mutable node metadata.
//  - child(loc, dir), setChild(loc, dir, child): read/write child links.
//  - parent(loc), setParent(loc, parent): read/write parent links.
//  - SequentialBuilder and beginSequentialBuild(count): create nodes in a
//    session that supports indexed access and rolls back uncommitted nodes.
//
// Optional capabilities such as clearAll(), reclaim(), and ordered-storage
// helpers are discovered separately by getCapabilities().
pub fn assertBaseRequirements(comptime Cache: type, comptime K: type, comptime V: type, comptime Tags: type) void {
    requireDecl(Cache, "Location");
    const Location = Cache.Location;
    const SelfPtr = *Cache;
    const LocPtr = *Location;
    const MaybeLoc = ?Location;

    requireDecl(Cache, "init");
    requireDecl(Cache, "deinit");
    requireDecl(Cache, "create");
    requireDecl(Cache, "destroy");
    requireDecl(Cache, "fastDeinitAllowed");
    requireDecl(Cache, "eq");
    requireDecl(Cache, "keyPtr");
    requireDecl(Cache, "valuePtr");
    requireDecl(Cache, "meta");
    requireDecl(Cache, "child");
    requireDecl(Cache, "setChild");
    requireDecl(Cache, "parent");
    requireDecl(Cache, "setParent");
    requireDecl(Cache, "SequentialBuilder");
    requireDecl(Cache, "beginSequentialBuild");

    requireErrorUnionMethod(@TypeOf(Cache.init), "init", &.{std.mem.Allocator}, Cache);
    requireMethod(@TypeOf(Cache.deinit), "deinit", &.{SelfPtr}, void);
    requireErrorUnionMethod(@TypeOf(Cache.create), "create", &.{SelfPtr}, Location);
    requireMethod(@TypeOf(Cache.destroy), "destroy", &.{ SelfPtr, Location }, void);
    requireMethod(@TypeOf(Cache.fastDeinitAllowed), "fastDeinitAllowed", &.{SelfPtr}, bool);
    requireMethod(@TypeOf(Cache.eq), "eq", &.{ SelfPtr, Location, Location }, bool);
    requireMethod(@TypeOf(Cache.keyPtr), "keyPtr", &.{ SelfPtr, Location }, *K);
    requireMethod(@TypeOf(Cache.valuePtr), "valuePtr", &.{ SelfPtr, Location }, *V);
    requireMethod(@TypeOf(Cache.meta), "meta", &.{ SelfPtr, Location }, Meta(Tags));
    requireDirMethod(@TypeOf(Cache.child), "child", &.{ SelfPtr, Location, direction }, MaybeLoc);
    requireDirMethod(@TypeOf(Cache.setChild), "setChild", &.{ SelfPtr, LocPtr, direction, MaybeLoc }, void);
    requireMethod(@TypeOf(Cache.parent), "parent", &.{ SelfPtr, Location }, MaybeLoc);
    requireMethod(@TypeOf(Cache.setParent), "setParent", &.{ SelfPtr, LocPtr, MaybeLoc }, void);

    const Builder = Cache.SequentialBuilder;
    const BuilderPtr = *Builder;
    requireErrorUnionMethod(@TypeOf(Cache.beginSequentialBuild), "beginSequentialBuild", &.{ SelfPtr, usize }, Builder);
    requireErrorUnionMethod(@TypeOf(Builder.prepare), "SequentialBuilder.prepare", &.{BuilderPtr}, void);
    requireErrorUnionMethod(@TypeOf(Builder.append), "SequentialBuilder.append", &.{BuilderPtr}, Location);
    requireMethod(@TypeOf(Builder.locationAt), "SequentialBuilder.locationAt", &.{ BuilderPtr, usize }, Location);
    requireMethod(@TypeOf(Builder.commit), "SequentialBuilder.commit", &.{BuilderPtr}, void);
    requireMethod(@TypeOf(Builder.deinit), "SequentialBuilder.deinit", &.{BuilderPtr}, void);
}

// Capabilities is computed from a concrete cache implementation and describes
// optional cache operations that the tree can use when they are available.
pub const Capabilities = struct {
    hasFastClear: bool,
    hasCompactStorage: bool,
    hasOrderedStorage: bool,
};

pub fn getCapabilities(comptime Cache: type) Capabilities {
    const has_indexed_storage = @hasDecl(Cache, "locationAt");
    return .{
        .hasFastClear = @hasDecl(Cache, "clearAll"),
        .hasCompactStorage = @hasDecl(Cache, "reclaim"),
        .hasOrderedStorage = @hasDecl(Cache, "relocate") and
            @hasDecl(Cache, "finishOrderStorage") and
            has_indexed_storage and
            @hasDecl(Cache, "nextLocation") and
            @hasDecl(Cache, "prevLocation"),
    };
}

const fast_deinit_alloc_addrs = blk: {
    var arena: std.heap.ArenaAllocator = undefined;
    const arena_allocator = arena.allocator();
    var fixed_buffer: std.heap.FixedBufferAllocator = undefined;
    const fixed_buffer_allocator = fixed_buffer.allocator();
    break :blk [_]*const anyopaque{
        @ptrCast(@alignCast(arena_allocator.vtable.alloc)),
        @ptrCast(@alignCast(fixed_buffer_allocator.vtable.alloc)),
    };
};

// fastDeinitAllowed returns true for allocators that can release all tree-owned
// node memory at once, so the tree can skip walking and destroying every node.
pub fn fastDeinitAllowed(a: std.mem.Allocator) bool {
    const alloc_addr: *const anyopaque = @ptrCast(@alignCast(a.vtable.alloc));
    inline for (fast_deinit_alloc_addrs) |ptr| {
        if (alloc_addr == ptr) return true;
    }
    return false;
}

test "fastDeinitAllowed ArenaAllocator" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    try std.testing.expect(fastDeinitAllowed(arena.allocator()));
    defer arena.deinit();
}

test "fastDeinitAllowed FixedBufferAllocator" {
    var buff: [16 * 1024]u8 = undefined;
    var fb = std.heap.FixedBufferAllocator.init(&buff);
    try std.testing.expect(fastDeinitAllowed(fb.allocator()));
}

test "fastDeinitAllowed std.testing.allocator" {
    try std.testing.expect(!fastDeinitAllowed(std.testing.allocator));
}

test "indexed sequential builder rejects an unexpected location" {
    const BrokenCache = struct {
        const Self = @This();
        pub const Location = usize;

        destroy_count: usize = 0,

        pub fn reserveNodes(_: *Self, _: usize) !void {}

        pub fn create(_: *Self) !Location {
            return 1;
        }

        pub fn eq(_: *Self, lhs: Location, rhs: Location) bool {
            return lhs == rhs;
        }

        pub fn locationAt(_: *Self, pos: usize) Location {
            return pos;
        }

        pub fn destroy(self: *Self, _: Location) void {
            self.destroy_count += 1;
        }
    };

    var cache = BrokenCache{};
    const Builder = MakeIndexedSequentialBuilder(BrokenCache);
    var builder = Builder.init(&cache, 1);

    try builder.prepare();
    try std.testing.expectError(error.InvalidSequentialLocation, builder.append());
    try std.testing.expectEqual(@as(usize, 1), cache.destroy_count);

    builder.deinit();
    try std.testing.expectEqual(@as(usize, 1), cache.destroy_count);
}
