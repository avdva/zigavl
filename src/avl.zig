const std = @import("std");
const math = std.math;
const direction = @import("direction.zig").direction;
const ptrLocationCache = @import("ptr_location.zig").LocationCache;
const llLocationCache = @import("ll_location.zig").LocationCache;
const arrayLocationCache = @import("array_location.zig").LocationCache;

pub const NodeCacheType = enum(u8) {
    PointerBased,
    ListBased,
    ArrayBased,
};

// Options defines some comptime parameters of the tree type.
pub const Options = struct {
    // countChildren, if set, enables children counts for every node of the tree.
    // the number of children allows to locate a node by its position with a guaranteed complexity O(logn).
    countChildren: bool = false,
    nodeCacheType: NodeCacheType = .PointerBased,
    debug: bool = false,
};

// InitOptions defines some runtime parameters of the tree instance.
pub const InitOptions = struct {
    // allowFastDeinit speeds up deinit() call by making it a no-op in cases
    // where all the memory can be freed on the allocator level.
    // normally, deinit() traverses the tree removing each node, however,
    // this might not be necessary, if certain types of allocators are used.
    // enum values:
    //  always - deinit() never deletes the nodes.
    //  auto - deinit() does not delete the nodes,
    //    if std.heap.ArenaAllocator or std.heap.FixedBufferAllocator are for allocations.
    //  never[default] - deinit() always deletes the nodes.
    allowFastDeinit: enum { always, auto, never } = .never,
};

// Tree is a generic avl tree.
// AVL tree (https://en.wikipedia.org/wiki/AVL_tree) is a self-balancing binary search tree.
// For each node of the tree the heights of the left and right sub-trees differ by at most one.
// Find and Delete operations have O(logn) complexity.
//  K - key type
//  V - value type
//  Cmp - a comparator.
pub fn Tree(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order) type {
    return TreeWithOptions(K, V, Cmp, .{});
}

// TreeWithOptions acts like Tree func, but also accepts compile-known Options.
pub fn TreeWithOptions(comptime K: type, comptime V: type, comptime Cmp: fn (a: K, b: K) math.Order, comptime options: Options) type {
    return struct {
        const Self = @This();
        const Tags = if (options.countChildren)
            struct { childrenCount: u32 = 0 }
        else
            struct {};

        const KeyType = K;
        const ValueType = V;
        const Cache = blk: {
            const cacheType = switch (options.nodeCacheType) {
                .ListBased => llLocationCache(K, V, Tags),
                .ArrayBased => arrayLocationCache(K, V, Tags),
                .PointerBased => ptrLocationCache(K, V, Tags),
            };
            if (options.debug) {
                break :blk TestLocationCache(cacheType);
            }
            break :blk cacheType;
        };
        const Location = Cache.Location;
        const Comparer = Cmp;
        const TreeOptions = options;

        const LocateResult = struct {
            loc: ?Location,
            dir: direction,
        };

        pub const Entry = struct {
            Key: K,
            Value: *V,
        };

        fn locEq(self: *Self, lhs: Location, rhs: Location) bool {
            return self.lc.eq(lhs, rhs);
        }

        fn data(self: *Self, loc: Location) *Location.NodeData {
            return self.lc.data(loc);
        }

        fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            return self.lc.child(loc, dir);
        }

        fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            self.lc.setChild(loc, dir, child_loc);
        }

        fn parent(self: *Self, loc: Location) ?Location {
            return self.lc.parent(loc);
        }

        fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.lc.setParent(loc, p);
        }

        fn goLeft(self: *Self, loc: Location) Location {
            var l = loc;
            while (true) {
                const left = self.child(l, .left) orelse break;
                l = left;
            }
            return l;
        }

        fn goRight(self: *Self, loc: Location) Location {
            var r = loc;
            while (true) {
                const right = self.child(r, .right) orelse break;
                r = right;
            }
            return r;
        }

        fn nextInOrderLocation(self: *Self, loc: Location) ?Location {
            var l = loc;
            if (self.child(l, .right)) |r| {
                return self.goLeft(r);
            }
            while (true) {
                const p = self.parent(l) orelse return null;
                const dir = self.childDir(p, l);
                if (dir == .left or dir == .center) {
                    return p;
                }
                l = p;
            }
        }

        fn prevInOrderLocation(self: *Self, loc: Location) ?Location {
            var l = loc;
            if (self.child(l, .left)) |left| {
                return self.goRight(left);
            }
            while (true) {
                const p = self.parent(l) orelse return null;
                const dir = self.childDir(p, l);
                if (dir == .right or dir == .center) {
                    return p;
                }
                l = p;
            }
        }

        fn goLeftRight(self: *Self, loc: Location) ?Location {
            var l = loc;
            while (true) {
                l = self.goLeft(l);
                var right = self.child(l, .right) orelse return l;
                while (true) {
                    if (self.child(right, .left)) |right_left| {
                        l = right_left;
                        break;
                    }
                    if (self.child(right, .right)) |right_right| {
                        right = right_right;
                    } else {
                        return right;
                    }
                }
            }
            return l;
        }

        fn nextPostOrderLocation(self: *Self, loc: Location) ?Location {
            const l = loc;
            const p = self.parent(l) orelse return null;
            const dir = self.childDir(p, l);
            switch (dir) {
                .left => {
                    const right = self.child(p, .right) orelse return p;
                    return self.goLeftRight(right);
                },
                .right => return p,
                else => unreachable,
            }
        }

        fn advance(self: *Self, loc: Location, count: isize) Location {
            var res = loc;
            var c = count;
            while (c > 0) {
                res = self.nextInOrderLocation(res) orelse return res;
                c -= 1;
            }
            while (c < 0) {
                res = self.prevInOrderLocation(res) orelse return res;
                c += 1;
            }
            return res;
        }

        fn reparent(self: *Self, p: ?Location, dir: direction, child_loc: ?Location) void {
            if (p) |parent_loc| {
                self.setChildAt(parent_loc, dir, child_loc);
            }
            if (child_loc) |c| {
                var ch = c;
                self.setParent(&ch, p);
            }
        }

        fn childAt(self: *Self, loc: Location, dir: direction) ?Location {
            switch (dir) {
                .left => return self.child(loc, .left),
                .right => return self.child(loc, .right),
                else => unreachable,
            }
        }

        fn setChildAt(self: *Self, parent_loc: Location, dir: direction, child_loc: ?Location) void {
            var p = parent_loc;
            switch (dir) {
                .left => self.setChild(&p, .left, child_loc),
                .right => self.setChild(&p, .right, child_loc),
                else => unreachable,
            }
        }

        fn childDir(self: *Self, loc: Location, other: Location) direction {
            if (self.child(loc, .left)) |left| {
                if (self.locEq(left, other)) {
                    return .left;
                }
            }
            if (self.child(loc, .right)) |right| {
                if (self.locEq(right, other)) {
                    return .right;
                }
            }
            return .center;
        }

        fn recalcCounts(self: *Self, loc: Location) void {
            var count: u32 = 0;
            if (self.child(loc, .left)) |left| {
                count += 1 + self.data(left).tags.childrenCount;
            }
            if (self.child(loc, .right)) |right| {
                count += 1 + self.data(right).tags.childrenCount;
            }
            self.data(loc).tags.childrenCount = count;
        }

        fn updateCounts(self: *Self, loc: Location) void {
            var mutLoc: ?Location = loc;
            while (mutLoc) |*l| {
                self.recalcCounts(l.*);
                mutLoc = self.parent(l.*);
            }
        }

        fn leftCount(self: *Self, loc: Location) usize {
            if (self.child(loc, .left)) |left| {
                return 1 + self.data(left).tags.childrenCount;
            }
            return 0;
        }

        fn recalcHeight(self: *Self, loc: Location) bool {
            var h: u8 = 0;
            if (self.child(loc, .left)) |l| {
                h = 1 + self.data(l).h;
            }
            if (self.child(loc, .right)) |r| {
                h = @max(h, 1 + self.data(r).h);
            }
            return self.data(loc).setHeight(h);
        }

        fn balance(self: *Self, loc: Location) i8 {
            var b: i8 = 0;
            if (self.child(loc, .right)) |right| {
                b += 1 + @as(i8, @intCast(self.data(right).h));
            }
            if (self.child(loc, .left)) |left| {
                b -= 1 + @as(i8, @intCast(self.data(left).h));
            }
            return b;
        }

        // Iterator traverses the tree.
        pub const Iterator = struct {
            tree: *Self,
            loc: ?Location,

            fn init(tree: *Self, loc: ?Location) Iterator {
                return Iterator{
                    .tree = tree,
                    .loc = loc,
                };
            }

            pub fn next(self: *Iterator) void {
                if (self.loc) |l| {
                    self.loc = self.tree.nextInOrderLocation(l);
                }
            }

            pub fn prev(self: *Iterator) void {
                if (self.loc) |l| {
                    self.loc = self.tree.prevInOrderLocation(l);
                }
            }

            pub fn value(self: *const Iterator) ?Entry {
                if (self.loc) |l| {
                    const data_ptr = self.tree.data(l);
                    return Entry{
                        .Key = data_ptr.k,
                        .Value = &data_ptr.v,
                    };
                }
                return null;
            }
        };

        io: InitOptions,
        lc: Cache,
        length: usize,
        root: ?Location,
        min: ?Location,
        max: ?Location,

        // init initializes the tree.
        pub fn init(a: std.mem.Allocator) !Self {
            return Self.initWithOptions(a, .{});
        }

        // initWithOptions initializes the tree.
        pub fn initWithOptions(a: std.mem.Allocator, io: InitOptions) !Self {
            return Self{
                .lc = try Cache.init(a),
                .length = 0,
                .root = null,
                .min = null,
                .max = null,
                .io = io,
            };
        }

        // deinit releases the memory taken by all the nodes.
        // Time complexity:
        //  O(1) - if fast deinit is enabled (see InitOptions.allowFastDeinit).
        //  O(n) - otherwise.
        pub fn deinit(self: *Self) void {
            defer self.lc.deinit();
            if (self.io.allowFastDeinit == .always or self.io.allowFastDeinit == .auto and self.lc.fastDeinitAllowed()) {
                return;
            }
            const min = self.min orelse return;
            var loc = self.goLeftRight(min);
            while (true) {
                const l = loc orelse break;
                const next = self.nextPostOrderLocation(l);
                self.lc.destroy(l);
                loc = next;
            }
        }

        // len returns the number of elements.
        pub fn len(self: *const Self) usize {
            return self.length;
        }

        fn createNewNode(self: *Self, k: ?K, v: ?V) !Location {
            const new_loc = try self.lc.create();
            const data_ptr = self.data(new_loc);
            data_ptr.*.tags = .{};
            if (k) |kVal| {
                data_ptr.*.k = kVal;
            }
            if (v) |vVal| {
                data_ptr.*.v = vVal;
            }
            return new_loc;
        }

        // InsertResult is returned from any function that inserts data to the tree.
        //  inserted == true if a new node was added to the tree.
        //  v - a pointer to the data, existing before the call, or the newly added.
        pub const InsertResult = struct {
            inserted: bool,
            v: *V,
        };

        // getOrEmplace inserts a new kv pair into the tree.
        //  - if tree already contains 'k', the function returns InsertResult{.inserted = false, .v = ptr_to_existing_value}
        //  - otherwise calls ctor with given args to initialise a newly created value.
        // Time complexity: O(logn).
        pub fn getOrEmplace(self: *Self, k: K, ctor: fn (v: *V, args: anytype) void, args: anytype) !InsertResult {
            const res = self.locate(k);
            if (res.loc) |l| {
                if (res.dir == .center) {
                    return InsertResult{
                        .inserted = false,
                        .v = &self.data(l).v,
                    };
                }
            }
            const new_loc = try self.createNewNode(k, null);
            ctor(&self.data(new_loc).v, args);
            self.insertNew(res, new_loc);
            return InsertResult{
                .inserted = true,
                .v = &self.data(new_loc).v,
            };
        }

        // getOrInsert inserts a new kv pair into the tree if tke key is not present.
        // Time complexity: O(logn).
        pub fn getOrInsert(self: *Self, k: K, v: V) !InsertResult {
            return self.doInsert(k, v, false);
        }

        // insert inserts a node into the tree.
        // If the key `k` was present in the tree, node's value is updated to `v`.
        // Time complexity: O(logn).
        pub fn insert(self: *Self, k: K, v: V) !InsertResult {
            return self.doInsert(k, v, true);
        }

        fn doInsert(self: *Self, k: K, v: V, updateExisting: bool) !InsertResult {
            const res = self.locate(k);
            if (res.loc) |l| {
                if (res.dir == .center) {
                    if (updateExisting) {
                        self.data(l).v = v;
                    }
                    return InsertResult{
                        .inserted = false,
                        .v = &self.data(l).v,
                    };
                }
            }
            const new_loc = try self.createNewNode(k, v);
            self.insertNew(res, new_loc);
            return InsertResult{
                .inserted = true,
                .v = &self.data(new_loc).v,
            };
        }

        fn insertNew(self: *Self, where: LocateResult, new_loc: Location) void {
            self.length += 1;
            switch (where.dir) {
                .left, .right => {
                    const l = where.loc orelse unreachable;
                    self.reparent(l, where.dir, new_loc);
                    if (where.dir == .left and self.locEq(l, self.min.?)) {
                        self.min = new_loc;
                    } else if (where.dir == .right and self.locEq(l, self.max.?)) {
                        self.max = new_loc;
                    }
                    if (self.recalcHeight(l)) {
                        if (options.countChildren) {
                            self.recalcCounts(l);
                        }
                        self.checkBalance(self.parent(l), false);
                    } else {
                        if (options.countChildren) {
                            self.updateCounts(l);
                        }
                    }
                },
                .center => {
                    self.root = new_loc;
                    self.min = new_loc;
                    self.max = new_loc;
                },
            }
        }

        fn deleteLocation(self: *Self, loc: Location) void {
            self.deleteAndReplace(loc);
            self.lc.destroy(loc);
        }

        // delete deletes a node from the tree.
        // Returns the value associated with k, if the node was present in the tree.
        // Time complexity: O(logn).
        pub fn delete(self: *Self, k: K) ?V {
            const res = self.locate(k);
            if (res.dir != .center) {
                return null;
            }
            const l = res.loc orelse return null;
            const v = self.data(l).v;
            self.deleteLocation(l);
            return v;
        }

        fn deleteAndReplace(self: *Self, loc: Location) void {
            const replacement = self.findReplacement(loc);
            if (self.min) |min| {
                if (self.locEq(loc, min)) {
                    self.min = self.nextInOrderLocation(loc);
                }
            }
            if (self.max) |max| {
                if (self.locEq(loc, max)) {
                    self.max = self.prevInOrderLocation(loc);
                }
            }
            const parent_loc = self.parent(loc);
            self.length -= 1;
            if (replacement) |rep| {
                const replacement_parent = self.parent(rep).?;
                const replacement_dir = self.childDir(replacement_parent, rep);
                const inverted = replacement_dir.invert();
                if (self.locEq(replacement_parent, loc)) {
                    if (parent_loc) |p| {
                        self.reparent(p, self.childDir(p, loc), rep);
                    } else {
                        self.setRoot(rep);
                    }
                    self.reparent(rep, inverted, self.childAt(loc, inverted));
                    self.checkBalance(rep, true);
                    return;
                }
                const replacement_child = self.childAt(rep, inverted);
                self.reparent(replacement_parent, replacement_dir, replacement_child);
                if (parent_loc) |p| {
                    self.reparent(p, self.childDir(p, loc), rep);
                } else {
                    self.setRoot(rep);
                }
                self.reparent(rep, .left, self.child(loc, .left));
                self.reparent(rep, .right, self.child(loc, .right));
                self.checkBalance(replacement_parent, true);
            } else {
                if (parent_loc) |p| {
                    self.reparent(p, self.childDir(p, loc), replacement);
                    self.checkBalance(p, false);
                } else {
                    self.setRoot(null);
                }
            }
        }

        fn findReplacement(self: *Self, loc: Location) ?Location {
            const left = self.child(loc, .left);
            const right = self.child(loc, .right);
            if (left) |l| {
                if (right) |r| {
                    // Russell A. Brown, Optimized Deletion From an AVL Tree.
                    // https://arxiv.org/pdf/2406.05162v5
                    if (self.balance(loc) <= 0) {
                        return self.goRight(l);
                    }
                    return self.goLeft(r);
                }
                return left;
            }
            return right;
        }

        // getMin returns the minimum element of the tree.
        // Time complexity: O(1).
        pub fn getMin(self: *Self) ?Entry {
            if (self.min) |min| {
                const data_ptr = self.data(min);
                return Entry{
                    .Key = data_ptr.k,
                    .Value = &data_ptr.v,
                };
            }
            return null;
        }

        // getMax returns the maximum element of the tree.
        // Time complexity: O(1).
        pub fn getMax(self: *Self) ?Entry {
            if (self.max) |max| {
                const data_ptr = self.data(max);
                return Entry{
                    .Key = data_ptr.k,
                    .Value = &data_ptr.v,
                };
            }
            return null;
        }

        // ascendFromStart returns an iterator pointing to the first element.
        // Time complexity: O(1).
        pub fn ascendFromStart(self: *Self) Iterator {
            return Iterator{
                .tree = self,
                .loc = self.min,
            };
        }

        // descendFromEnd returns an iterator pointing to the last element.
        // Time complexity: O(1).
        pub fn descendFromEnd(self: *Self) Iterator {
            return Iterator{
                .tree = self,
                .loc = self.max,
            };
        }

        // deleteIterator deletes an iterator from the tree and returns
        // an iterator to the next element.
        pub fn deleteIterator(self: *Self, it: Iterator) Iterator {
            std.debug.assert(it.tree == self);
            const loc = it.loc orelse return it;
            const next = self.nextInOrderLocation(loc);
            self.deleteLocation(loc);
            return Iterator{
                .loc = next,
                .tree = self,
            };
        }

        // get returns a value for key k.
        // Time complexity: O(logn).
        pub fn get(self: *Self, k: K) ?*V {
            const res = self.locate(k);
            if (res.dir == .center) {
                if (res.loc) |loc| {
                    return &self.data(loc).v;
                }
            }
            return null;
        }

        // at returns a an entry at the ith position of the sorted array.
        // Panics if position >= tree.Len().
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn at(self: *Self, pos: usize) Entry {
            const loc = self.locateAt(pos);
            const data_ptr = self.data(loc);
            return Entry{
                .Key = data_ptr.k,
                .Value = &data_ptr.v,
            };
        }

        // ascendAt returns an iterator pointing to the ith element.
        // Panics if position >= tree.Len().
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn ascendAt(self: *Self, pos: usize) Iterator {
            const loc = self.locateAt(pos);
            return Iterator{
                .tree = self,
                .loc = loc,
            };
        }

        // KV is a key-value pair.
        pub const KV = struct {
            Key: K,
            Value: V,
        };

        // deleteAt deletes a node at the given position.
        // Panics if position >= tree.Len().
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn deleteAt(self: *Self, pos: usize) KV {
            const loc = self.locateAt(pos);
            const data_ptr = self.data(loc);
            const kv = KV{
                .Key = data_ptr.k,
                .Value = data_ptr.v,
            };
            self.deleteLocation(loc);
            return kv;
        }

        fn setRoot(self: *Self, loc: ?Location) void {
            self.root = loc;
            if (self.root) |*root| {
                self.setParent(root, null);
            }
        }

        fn treeRotated(self: *Self, parent_loc: ?Location, oldRoot: Location, newRoot: Location) void {
            if (parent_loc) |p| {
                self.reparent(p, self.childDir(p, oldRoot), newRoot);
            } else {
                self.setRoot(newRoot);
            }
        }

        fn checkBalance(self: *Self, loc: ?Location, all_way_up: bool) void {
            var mutLoc = loc;
            while (mutLoc) |*mlPtr| {
                const l = mlPtr.*;
                const parent_loc = self.parent(l);
                switch (self.balance(l)) {
                    -2 => {
                        const subRoot = blk: {
                            switch (self.balance(self.child(l, .left).?)) {
                                -1, 0 => {
                                    break :blk self.rr(l);
                                },
                                1 => {
                                    break :blk self.lr(l);
                                },
                                else => unreachable,
                            }
                        };
                        self.treeRotated(parent_loc, l, subRoot);
                    },
                    2 => {
                        const subRoot = blk: {
                            switch (self.balance(self.child(l, .right).?)) {
                                -1 => {
                                    break :blk self.rl(l);
                                },
                                0, 1 => {
                                    break :blk self.ll(l);
                                },
                                else => unreachable,
                            }
                        };
                        self.treeRotated(parent_loc, l, subRoot);
                    },
                    else => {
                        if (!self.recalcHeight(l) and !all_way_up) {
                            if (options.countChildren) {
                                self.updateCounts(l);
                            }
                            return;
                        }
                        if (options.countChildren) {
                            self.recalcCounts(l);
                        }
                    },
                }
                mutLoc = parent_loc;
            }
        }

        fn rr(self: *Self, loc: Location) Location {
            const l = loc;
            const left = self.child(l, .left).?;
            const left_right = self.child(left, .right);

            self.reparent(l, .left, left_right);
            self.reparent(left, .right, l);

            _ = self.recalcHeight(l);
            _ = self.recalcHeight(left);

            if (options.countChildren) {
                self.recalcCounts(l);
                self.recalcCounts(left);
            }

            return left;
        }

        fn lr(self: *Self, loc: Location) Location {
            const l = loc;
            const left = self.child(l, .left).?;
            const left_right = self.child(left, .right).?;
            const left_right_right = self.child(left_right, .right);
            const left_right_left = self.child(left_right, .left);

            self.reparent(left_right, .right, l);
            self.reparent(left_right, .left, left);

            self.reparent(l, .left, left_right_right);
            self.reparent(left, .right, left_right_left);

            _ = self.recalcHeight(l);
            _ = self.recalcHeight(left);
            _ = self.recalcHeight(left_right);

            if (options.countChildren) {
                self.recalcCounts(l);
                self.recalcCounts(left);
                self.recalcCounts(left_right);
            }

            return left_right;
        }

        fn rl(self: *Self, loc: Location) Location {
            const l = loc;
            const right = self.child(l, .right).?;
            const right_left = self.child(right, .left).?;

            const right_left_left = self.child(right_left, .left);
            const right_left_right = self.child(right_left, .right);

            self.reparent(right_left, .left, l);
            self.reparent(right_left, .right, right);

            self.reparent(l, .right, right_left_left);
            self.reparent(right, .left, right_left_right);

            _ = self.recalcHeight(l);
            _ = self.recalcHeight(right);
            _ = self.recalcHeight(right_left);

            if (options.countChildren) {
                self.recalcCounts(l);
                self.recalcCounts(right);
                self.recalcCounts(right_left);
            }

            return right_left;
        }

        fn ll(self: *Self, loc: Location) Location {
            const l = loc;
            const right = self.child(l, .right).?;
            const right_left = self.child(right, .left);

            self.reparent(l, .right, right_left);
            self.reparent(right, .left, l);

            _ = self.recalcHeight(l);
            _ = self.recalcHeight(right);

            if (options.countChildren) {
                self.recalcCounts(l);
                self.recalcCounts(right);
            }

            return right;
        }

        fn locate(self: *Self, k: K) LocateResult {
            var result = LocateResult{
                .loc = self.root,
                .dir = .center,
            };
            while (true) {
                const l = result.loc orelse break;
                var next: ?Location = null;
                switch (Comparer(k, self.data(l).k)) {
                    .lt => {
                        next = self.child(l, .left);
                        result.dir = .left;
                    },
                    .eq => {
                        result.dir = .center;
                        return result;
                    },
                    .gt => {
                        next = self.child(l, .right);
                        result.dir = .right;
                    },
                }
                if (next == null) {
                    break;
                }
                result.loc = next;
            }
            return result;
        }

        fn shouldLocateAtLinearly(self: *Self, pos: usize) bool {
            const p = @min(pos, self.length - pos - 1);
            return p <= 8;
        }

        fn locateAt(self: *Self, pos: usize) Location {
            if (pos >= self.len()) {
                @panic("index out of range");
            }
            if (!options.countChildren or self.shouldLocateAtLinearly(pos)) {
                if (pos < self.length / 2) {
                    return self.advance(self.min.?, @as(isize, @intCast(pos)));
                }
                return self.advance(self.max.?, -@as(isize, @intCast(self.length - pos - 1)));
            }
            var loc = self.root.?;
            var p = pos;
            while (true) {
                const left_count = self.leftCount(loc);
                if (p == left_count) {
                    return loc;
                }
                if (p < left_count) {
                    loc = self.child(loc, .left).?;
                } else {
                    p -= (left_count + 1);
                    loc = self.child(loc, .right).?;
                }
            }
        }
    };
}

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

test "empty tree" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var it = t.ascendFromStart();
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    try std.testing.expect(t.delete(0) == null);
}

test "tree getOrInsert" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();
    var ir = t.insert(1, 1) catch unreachable;
    try std.testing.expectEqual(true, ir.inserted);
    ir = try t.getOrInsert(1, 2);
    try std.testing.expectEqual(false, ir.inserted);
    try std.testing.expectEqual(@as(i64, 1), ir.v.*);
    ir = t.insert(1, 1) catch unreachable;
    try std.testing.expectEqual(false, ir.inserted);
    ir.v.* = 2;
    try std.testing.expectEqual(@as(i64, 2), t.get(1).?.*);
    ir = try t.getOrInsert(2, 2);
    try std.testing.expectEqual(@as(i64, 2), t.get(2).?.*);
    ir.v.* = 3;
    try std.testing.expectEqual(@as(i64, 3), t.get(2).?.*);
}

test "tree getOrEmplace" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();
    var i: i64 = 0;
    const ctor = struct {
        fn ctor(ptr: *i64, args: anytype) void {
            ptr.* = args;
        }
    }.ctor;
    while (i < 128) {
        const ir = try t.getOrEmplace(i, ctor, i);
        try std.testing.expect(ir.inserted);
        try std.testing.expectEqual(i, ir.v.*);
        try checkHeightAndBalance(&t);
        i += 1;
    }

    i = 0;
    while (i < 128) {
        const v = t.get(i);
        try std.testing.expect(v != null);
        try std.testing.expectEqual(i, v.?.*);
        i += 1;
    }

    i = 0;
    while (i < 128) {
        const ir = try t.getOrEmplace(i, ctor, i * 2);
        try std.testing.expect(!ir.inserted);
        try std.testing.expectEqual(i, ir.v.*);
        i += 1;
    }
}

test "tree insert" {
    const a = std.testing.allocator;
    const TreeType = Tree(i64, i64, i64Cmp);
    var t = try TreeType.init(a);
    defer t.deinit();
    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expectEqual(true, ir.inserted);
        try std.testing.expectEqual(i, ir.v.*);

        const min = t.getMin();
        try std.testing.expect(min != null);
        const exp: i64 = 0;
        try std.testing.expectEqual(exp, min.?.Key);
        try std.testing.expectEqual(exp, min.?.Value.*);

        const max = t.getMax();
        try std.testing.expect(max != null);
        try std.testing.expectEqual(i, max.?.Key);
        try std.testing.expectEqual(i, max.?.Value.*);

        try checkHeightAndBalance(&t);

        i += 1;
    }

    i = 0;
    while (i < 128) {
        const v = t.get(i);
        try std.testing.expect(v != null);
        try std.testing.expectEqual(i, v.?.*);
        i += 1;
    }

    i = 127;
    while (i >= 0) {
        const ir = try t.insert(i, i * 2);
        try std.testing.expect(!ir.inserted);
        try std.testing.expectEqual(i * 2, ir.v.*);
        try checkHeightAndBalance(&t);
        i -= 1;
    }

    i = 0;
    while (i < 128) {
        const v = t.get(i);
        try std.testing.expect(v != null);
        try std.testing.expectEqual(i * 2, v.?.*);
        i += 1;
    }
}

test "tree delete" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();
    var exp_len: usize = 0;
    try std.testing.expectEqual(exp_len, t.len());
    var ir = try t.insert(0, 0);
    try std.testing.expect(ir.inserted);
    var exp: i64 = 0;
    try std.testing.expectEqual(exp, t.delete(0).?);
    try checkHeightAndBalance(&t);

    ir = try t.insert(0, 0);
    try std.testing.expect(ir.inserted);
    ir = try t.insert(-1, -1);
    try std.testing.expect(ir.inserted);
    exp_len = 2;
    try std.testing.expectEqual(exp_len, t.len());
    try checkHeightAndBalance(&t);
    exp = 0;
    try std.testing.expectEqual(exp, t.delete(0).?);
    exp = -1;
    try std.testing.expectEqual(exp, t.delete(-1).?);
    exp_len = 0;
    try std.testing.expectEqual(exp_len, t.len());

    ir = try t.insert(0, 0);
    try std.testing.expect(ir.inserted);
    ir = try t.insert(1, 1);
    try std.testing.expect(ir.inserted);
    exp_len = 2;
    try std.testing.expectEqual(exp_len, t.len());
    try checkHeightAndBalance(&t);
    exp = 1;
    try std.testing.expectEqual(exp, t.delete(1).?);
    exp_len = 1;
    try std.testing.expectEqual(exp_len, t.len());
    try std.testing.expectEqual(@as(?i64, null), t.delete(-1));
    try checkHeightAndBalance(&t);
    exp = 0;
    try std.testing.expectEqual(exp, t.delete(0).?);
    exp_len = 0;
    try std.testing.expectEqual(exp_len, t.len());

    ir = try t.insert(0, 0);
    try std.testing.expect(ir.inserted);
    ir = try t.insert(1, 1);
    try std.testing.expect(ir.inserted);
    exp = 0;
    try std.testing.expectEqual(exp, t.delete(0).?);
    exp_len = 1;
    try std.testing.expectEqual(exp_len, t.len());
    try checkHeightAndBalance(&t);
    exp = 1;
    try std.testing.expectEqual(exp, t.delete(1).?);
    try checkHeightAndBalance(&t);
    exp_len = 0;
    try std.testing.expectEqual(exp_len, t.len());

    var i: i64 = 128;
    while (i >= 0) {
        ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        try std.testing.expectEqual(i, ir.v.*);
        i -= 1;
    }
    i = 128;
    while (i >= 0) {
        try std.testing.expectEqual(i, t.delete(i).?);
        try checkHeightAndBalance(&t);
        i -= 1;
    }
}

test "delete min" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i <= 128) {
        const e = t.getMin();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        try std.testing.expectEqual(i, t.delete(i).?);
        i += 1;
    }
    const exp_len: usize = 0;
    try std.testing.expectEqual(exp_len, t.len());
}

test "delete max" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i <= 128) {
        const e = t.getMax();
        try std.testing.expectEqual(128 - i, e.?.Key);
        try std.testing.expectEqual(128 - i, e.?.Value.*);
        try std.testing.expectEqual(128 - i, t.delete(128 - i).?);
        i += 1;
    }
    const exp_len: usize = 0;
    try std.testing.expectEqual(exp_len, t.len());
}

test "tree at_countChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    i = 0;
    while (i <= 128) {
        const e = t.at(@as(usize, @intCast(i)));
        try std.testing.expectEqual(i, e.Key);
        try std.testing.expectEqual(i, e.Value.*);
        i += 1;
    }
}

test "tree at_nocountChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i <= 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    i = 0;
    while (i <= 128) {
        const e = t.at(@as(usize, @intCast(i)));
        try std.testing.expectEqual(i, e.Key);
        try std.testing.expectEqual(i, e.Value.*);
        i += 1;
    }
}

test "tree deleteAt" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }

    var exp_len: usize = 128;
    i = 64;
    while (i < 128) {
        try std.testing.expectEqual(exp_len, t.len());
        const kv = t.deleteAt(64);
        try std.testing.expectEqual(i, kv.Key);
        try std.testing.expectEqual(i, kv.Value);
        i += 1;
        exp_len -= 1;
    }

    i = 0;
    while (i < 64) {
        try std.testing.expectEqual(exp_len, t.len());
        const kv = t.deleteAt(0);
        try std.testing.expectEqual(i, kv.Key);
        try std.testing.expectEqual(i, kv.Value);
        i += 1;
        exp_len -= 1;
    }
    try std.testing.expectEqual(exp_len, t.len());
}

test "tree iterator" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    var it = t.ascendFromStart();
    i = 0;
    while (i < 128) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.next();
        i += 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.descendFromEnd();
    i = 127;
    while (i >= 0) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.prev();
        i -= 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.ascendFromStart();
    i = 0;
    while (i < 64) {
        try std.testing.expect(it.value() != null);
        i += 1;
        it.next();
    }
    i = 0;
    while (i < 64) {
        const e = it.value();
        try std.testing.expectEqual(i + 64, e.?.Key);
        try std.testing.expectEqual(i + 64, e.?.Value.*);
        it = t.deleteIterator(it);
        i += 1;
    }

    it = t.ascendFromStart();
    i = 0;
    while (i < 64) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it = t.deleteIterator(it);
        i += 1;
    }

    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());
}

test "tree ascendAt" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var i: i64 = 0;
    while (i < 128) {
        const ir = try t.insert(i, i);
        try std.testing.expect(ir.inserted);
        i += 1;
    }
    i = 0;
    while (i < 128) {
        var it = t.ascendAt(@as(usize, @intCast(i)));
        var e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        var j = i - 1;
        while (j >= 0) {
            it.prev();
            e = it.value();
            try std.testing.expectEqual(j, e.?.Key);
            try std.testing.expectEqual(j, e.?.Value.*);
            j -= 1;
        }
        it = t.ascendAt(@as(usize, @intCast(i)));
        j = i + 1;
        while (j < t.len()) {
            it.next();
            e = it.value();
            try std.testing.expectEqual(j, e.?.Key);
            try std.testing.expectEqual(j, e.?.Value.*);
            j += 1;
        }
        i += 1;
    }
}

fn testTreeRandom(comptime options: Options) !void {
    var a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();
    var arr = try a.alloc(i64, 1024);
    for (arr, 0..) |_, idx| {
        arr[idx] = @as(i64, @intCast(idx));
    }
    defer a.free(arr);
    var i: i64 = 0;
    while (i < 10) {
        const exp_len: usize = 0;
        var r = std.Random.DefaultPrng.init(0);
        r.random().shuffle(i64, arr);
        for (arr) |val| {
            const ir = try t.insert(val, val);
            try std.testing.expect(ir.inserted);
            try std.testing.expectEqual(val, ir.v.*);
            try checkHeightAndBalance(&t);
        }
        r.random().shuffle(i64, arr);
        for (arr) |val| {
            try std.testing.expectEqual(val, t.delete(val).?);
            try checkHeightAndBalance(&t);
        }
        try std.testing.expectEqual(exp_len, t.len());
        i += 1;
    }
}

test "tree random (pointer cache)" {
    try testTreeRandom(.{ .countChildren = true, .nodeCacheType = .PointerBased });
}

test "tree random (list cache)" {
    try testTreeRandom(.{ .countChildren = true, .nodeCacheType = .ListBased });
}

test "tree random (array cache)" {
    try testTreeRandom(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
}

fn TestLocationCache(comptime underlying: type) type {
    return struct {
        const Self = @This();
        pub const Location = underlying.Location;

        u: underlying,

        destroyHook: ?*const fn (loc: Location) void,

        fn init(a: std.mem.Allocator) !Self {
            return Self{
                .u = try underlying.init(a),
                .destroyHook = null,
            };
        }

        fn deinit(_: *Self) void {}

        fn create(self: *Self) !Location {
            return self.u.create();
        }

        pub fn destroy(self: *Self, loc: Location) void {
            if (self.destroyHook) |dt| {
                dt(loc);
            }
            self.u.destroy(loc);
        }

        pub fn fastDeinitAllowed(self: *Self) bool {
            return self.u.fastDeinitAllowed();
        }

        pub fn eq(self: *Self, lhs: Location, rhs: Location) bool {
            return self.u.eq(lhs, rhs);
        }

        pub fn data(self: *Self, loc: Location) *Location.NodeData {
            return self.u.data(loc);
        }

        pub fn child(self: *Self, loc: Location, comptime dir: direction) ?Location {
            return self.u.child(loc, dir);
        }

        pub fn setChild(self: *Self, loc: *Location, comptime dir: direction, child_loc: ?Location) void {
            self.u.setChild(loc, dir, child_loc);
        }

        pub fn parent(self: *Self, loc: Location) ?Location {
            return self.u.parent(loc);
        }

        pub fn setParent(self: *Self, loc: *Location, p: ?Location) void {
            self.u.setParent(loc, p);
        }
    };
}

fn testFastDeinit(io: InitOptions, a: std.mem.Allocator, comptime nct: NodeCacheType) !void {
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{
        .nodeCacheType = nct,
        .debug = true,
    });
    var t = try TreeType.initWithOptions(a, io);
    defer t.deinit();
    t.lc.destroyHook = struct {
        fn doPanic(_: TreeType.Cache.Location) void {
            @panic("should not happen");
        }
    }.doPanic;
    _ = try t.insert(0, 0);
    _ = try t.insert(1, 1);
    _ = try t.insert(2, 2);
}

test "arena allocator: auto fast deinit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try testFastDeinit(.{ .allowFastDeinit = .auto }, arena.allocator(), .PointerBased);
}

test "arena allocator: always fast deinit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try testFastDeinit(.{ .allowFastDeinit = .always }, arena.allocator(), .PointerBased);
}

test "fixed buffer allocator: auto fast deinit" {
    var buff: [16 * 1024]u8 = undefined;
    var fb = std.heap.FixedBufferAllocator.init(&buff);
    try testFastDeinit(.{ .allowFastDeinit = .auto }, fb.allocator(), .PointerBased);
}

fn checkHeightAndBalance(tree: anytype) !void {
    _ = try recalcHeightAndBalance(@TypeOf(tree.*), tree, tree.root);
}

const recalcResult = struct {
    height: u8,
    l_count: u32,
    r_count: u32,

    fn init() recalcResult {
        return recalcResult{
            .height = 0,
            .l_count = 0,
            .r_count = 0,
        };
    }
};

fn recalcHeightAndBalance(comptime T: type, tree: *T, loc: ?T.Location) !recalcResult {
    var result = recalcResult.init();
    const l = loc orelse return result;
    if (tree.child(l, .left) != null) {
        const lRes = try recalcHeightAndBalance(T, tree, tree.child(l, .left));
        result.height = 1 + lRes.height;
        result.l_count = lRes.l_count + lRes.r_count + 1;
    }
    if (tree.child(l, .right) != null) {
        const rRes = try recalcHeightAndBalance(T, tree, tree.child(l, .right));
        result.height = @max(result.height, 1 + rRes.height);
        result.r_count = rRes.r_count + rRes.l_count + 1;
    }
    try std.testing.expectEqual(result.height, tree.data(l).h);
    if (tree.balance(l) < -1 or tree.balance(l) > 1) {
        return error{
            InvalidBalance,
        }.InvalidBalance;
    }
    return result;
}
