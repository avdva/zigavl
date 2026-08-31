const std = @import("std");
const math = std.math;
const cache = @import("cache.zig");
const cache_contract = @import("cache_contract.zig");
const direction = @import("direction.zig").direction;

pub const NodeCacheType = cache.NodeCacheType;

// Options defines compile-time parameters of the tree type.
pub const Options = struct {
    // countChildren, if set, enables children counts for every node of the tree.
    // the number of children allows to locate a node by its position with a guaranteed complexity O(logn).
    countChildren: bool = false,

    // nodeCacheType selects the node storage backend. PointerBased is the safest
    // default, ArrayBased favors locality with a pointer-stability caveat, and
    // StableArrayBased preserves pointer stability with chunked storage.
    nodeCacheType: cache.NodeCacheType = .PointerBased,
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
    const Tags = if (options.countChildren)
        struct { childrenCount: u32 = 0 }
    else
        struct {};
    const Cache = cache.Create(options.nodeCacheType, K, V, Tags);
    return InitTreeType(K, V, Cache, Cmp, options);
}

fn InitTreeType(comptime K: type, comptime V: type, comptime Cache: type, comptime Cmp: fn (a: K, b: K) math.Order, comptime options: Options) type {
    return struct {
        const Self = @This();

        const KeyType = K;
        const ValueType = V;

        const Location = Cache.Location;
        const Comparer = Cmp;
        const TreeOptions = options;

        const cacheCapabilities = cache_contract.getCapabilities(Cache);

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

        fn keyPtr(self: *Self, loc: Location) *K {
            return self.lc.keyPtr(loc);
        }

        fn valuePtr(self: *Self, loc: Location) *V {
            return self.lc.valuePtr(loc);
        }

        fn meta(self: *Self, loc: Location) Cache.Meta {
            return self.lc.meta(loc);
        }

        fn setHeight(self: *Self, loc: Location, height: u8) bool {
            const height_ptr = self.meta(loc).height;
            const old = height_ptr.*;
            height_ptr.* = height;
            return old != height;
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

        fn goRoot(self: *Self, loc: Location) Location {
            var r = loc;
            while (true) {
                const parent_loc = self.parent(r) orelse break;
                r = parent_loc;
            }
            return r;
        }

        // nextInOrderLocation returns the sorted successor of loc.
        // If loc has a right subtree, the successor is its leftmost node.
        // Otherwise, walk up until leaving a left edge.
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

        // prevInOrderLocation returns the sorted predecessor of loc.
        // It mirrors nextInOrderLocation: first try the rightmost node in the
        // left subtree, then walk up until leaving a right edge.
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

        // nextPostOrderLocation returns the next node in post-order traversal.
        // It is used by the normal deinit path, where children must be destroyed
        // before their parent. If loc is a left child and its parent has a right
        // subtree, traversal descends into that subtree first; otherwise the parent
        // itself is next.
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

        // advance moves loc by count sorted positions. Positive values move to
        // successors, negative values move to predecessors. If traversal reaches
        // either end before count is exhausted, the last valid location is returned.
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

        // reparent attaches child_loc as p's child at dir and updates the child's
        // parent pointer at the same time. Passing null for child_loc disconnects
        // that side of p; passing null for p makes child_loc parentless.
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

        // recalcCounts refreshes loc's cached subtree size from its direct children.
        // The stored value is the number of descendants, not including loc itself;
        // callers add one when they need a whole child subtree size.
        fn recalcCounts(self: *Self, loc: Location) void {
            var count: u32 = 0;
            if (self.child(loc, .left)) |left| {
                count += 1 + self.meta(left).tags.childrenCount;
            }
            if (self.child(loc, .right)) |right| {
                count += 1 + self.meta(right).tags.childrenCount;
            }
            self.meta(loc).tags.childrenCount = count;
        }

        // updateCounts walks from loc to the root after a structural change that
        // did not require a full rebalance walk, keeping ancestor descendant counts
        // consistent for rank and position-based operations.
        fn updateCounts(self: *Self, loc: Location) void {
            var mutLoc: ?Location = loc;
            while (mutLoc) |*l| {
                self.recalcCounts(l.*);
                mutLoc = self.parent(l.*);
            }
        }

        // leftCount returns the number of nodes in loc's left subtree. Rank helpers
        // use it to skip whole left subtrees without walking them.
        fn leftCount(self: *Self, loc: Location) usize {
            if (self.child(loc, .left)) |left| {
                return 1 + self.meta(left).tags.childrenCount;
            }
            return 0;
        }

        // recalcHeight refreshes loc's cached AVL height from its children.
        // It returns true when the height changed, which lets insertion rebalance
        // stop early once ancestors cannot be affected.
        fn recalcHeight(self: *Self, loc: Location) bool {
            var h: u8 = 0;
            if (self.child(loc, .left)) |l| {
                h = 1 + self.meta(l).height.*;
            }
            if (self.child(loc, .right)) |r| {
                h = @max(h, 1 + self.meta(r).height.*);
            }
            return self.setHeight(loc, h);
        }

        fn balance(self: *Self, loc: Location) i8 {
            var b: i8 = 0;
            if (self.child(loc, .right)) |right| {
                b += 1 + @as(i8, @intCast(self.meta(right).height.*));
            }
            if (self.child(loc, .left)) |left| {
                b -= 1 + @as(i8, @intCast(self.meta(left).height.*));
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
                    self.loc = self.tree.nextIteratorLocation(l);
                }
            }

            pub fn prev(self: *Iterator) void {
                if (self.loc) |l| {
                    self.loc = self.tree.prevIteratorLocation(l);
                }
            }

            pub fn value(self: *const Iterator) ?Entry {
                if (self.loc) |l| {
                    return Entry{
                        .Key = self.tree.keyPtr(l).*,
                        .Value = self.tree.valuePtr(l),
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
        storage_ordered: bool,

        // init initializes the tree with default options.
        pub fn init(a: std.mem.Allocator) !Self {
            return Self.initWithOptions(a, .{});
        }

        // initWithOptions initializes the tree with given options.
        pub fn initWithOptions(a: std.mem.Allocator, io: InitOptions) !Self {
            return Self{
                .lc = try Cache.init(a),
                .length = 0,
                .root = null,
                .min = null,
                .max = null,
                .storage_ordered = false,
                .io = io,
            };
        }

        fn destroyAllNodes(self: *Self) void {
            const min = self.min orelse return;
            var loc = self.goLeftRight(min);
            while (true) {
                const l = loc orelse break;
                const next = self.nextPostOrderLocation(l);
                self.lc.destroy(l);
                loc = next;
            }
        }

        fn resetTreeLinks(self: *Self) void {
            self.length = 0;
            self.root = null;
            self.min = null;
            self.max = null;
            self.storage_ordered = false;
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
            self.destroyAllNodes();
        }

        // clear removes all elements and releases node storage owned by the tree.
        // Complexity depends on node cache type:
        //  O(n) - PointerBased.
        //  O(1) - ArrayBased.
        //  O(number_of_chunks) - StableArrayBased.
        pub fn clear(self: *Self) void {
            if (cacheCapabilities.hasFastClear) {
                self.lc.clearAll();
            } else {
                self.destroyAllNodes();
            }
            self.resetTreeLinks();
        }

        // compactStorage asks the backing node cache to release storage kept by
        // removed nodes, when that cache supports compaction. It may move nodes,
        // invalidating existing iterators, locations, entries, and value pointers.
        // Caches without compaction support leave the tree untouched.
        pub fn compactStorage(self: *Self) void {
            if (!cacheCapabilities.hasCompactStorage) {
                return;
            }
            self.storage_ordered = false;
            self.root = self.lc.reclaim(0, self.root);
            if (self.root) |root| {
                self.min = self.goLeft(root);
                self.max = self.goRight(root);
            }
        }

        // orderStorageByKey moves nodes in address-based caches so sorted
        // position N is stored at address N. This enables O(1) lookup by sorted
        // index until the next structural mutation. It may move nodes,
        // invalidating existing iterators, locations, entries, and value pointers.
        // Caches without ordering support leave the tree untouched.
        pub fn orderStorageByKey(self: *Self) void {
            if (!cacheCapabilities.hasOrderedStorage) {
                return;
            }
            if (self.length == 0) {
                self.lc.finishOrderStorage(0);
                self.storage_ordered = false;
                return;
            }

            self.min = self.lc.relocate(self.min.?, 0);
            var loc = self.nextInOrderLocation(self.min.?);
            var pos: usize = 1;
            while (loc) |current| {
                const moved = self.lc.relocate(current, pos);
                loc = self.nextInOrderLocation(moved);
                pos += 1;
            }

            self.lc.finishOrderStorage(self.length);

            self.root = self.goRoot(self.min.?);
            self.max = self.goRight(self.root.?);
            self.storage_ordered = true;
        }

        // len returns the number of elements.
        pub fn len(self: *const Self) usize {
            return self.length;
        }

        fn createNewNode(self: *Self, k: ?K, v: ?V) !Location {
            const new_loc = try self.lc.create();
            const m = self.meta(new_loc);
            m.tags.* = .{};
            m.height.* = 0;
            if (k) |kVal| {
                self.keyPtr(new_loc).* = kVal;
            }
            if (v) |vVal| {
                self.valuePtr(new_loc).* = vVal;
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
                        .v = self.valuePtr(l),
                    };
                }
            }
            const new_loc = try self.createNewNode(k, null);
            ctor(self.valuePtr(new_loc), args);
            self.insertNew(res, new_loc);
            return InsertResult{
                .inserted = true,
                .v = self.valuePtr(new_loc),
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
                        self.valuePtr(l).* = v;
                    }
                    return InsertResult{
                        .inserted = false,
                        .v = self.valuePtr(l),
                    };
                }
            }
            const new_loc = try self.createNewNode(k, v);
            self.insertNew(res, new_loc);
            return InsertResult{
                .inserted = true,
                .v = self.valuePtr(new_loc),
            };
        }

        fn insertNew(self: *Self, where: LocateResult, new_loc: Location) void {
            if (comptime cacheCapabilities.hasOrderedStorage) {
                self.storage_ordered = false;
            }
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
            if (comptime cacheCapabilities.hasOrderedStorage) {
                self.storage_ordered = false;
            }
            self.deleteAndReplace(loc);
            self.lc.destroy(loc);
        }

        // canUpdateKeyInPlace checks whether new_key still belongs between loc's
        // in-order neighbors. If it does, changing only the key preserves the BST
        // ordering and avoids delete+insert work.
        fn canUpdateKeyInPlace(self: *Self, loc: Location, new_key: K) bool {
            if (self.prevInOrderLocation(loc)) |prev| {
                if (Comparer(self.keyPtr(prev).*, new_key) != .lt) {
                    return false;
                }
            }
            if (self.nextInOrderLocation(loc)) |next| {
                if (Comparer(new_key, self.keyPtr(next).*) != .lt) {
                    return false;
                }
            }
            return true;
        }

        fn resetDetachedLocation(self: *Self, loc: Location, k: K, v: V) void {
            var mut_loc = loc;
            self.setChild(&mut_loc, .left, null);
            self.setChild(&mut_loc, .right, null);
            self.setParent(&mut_loc, null);

            const m = self.meta(loc);
            m.tags.* = .{};
            m.height.* = 0;
            self.keyPtr(loc).* = k;
            self.valuePtr(loc).* = v;
        }

        // updateKey changes a node key while preserving its value.
        // If new_key already exists, the old value replaces the existing value
        // and old_key is removed. Returns null when old_key is not present.
        // Time complexity: O(logn).
        pub fn updateKey(self: *Self, old_key: K, new_key: K) ?*V {
            const old_res = self.locate(old_key);
            if (old_res.dir != .center) {
                return null;
            }
            const old_loc = old_res.loc orelse return null;

            if (Comparer(self.keyPtr(old_loc).*, new_key) == .eq) {
                self.keyPtr(old_loc).* = new_key;
                return self.valuePtr(old_loc);
            }

            const new_res = self.locate(new_key);
            if (new_res.dir == .center) {
                const new_loc = new_res.loc orelse unreachable;
                const old_value = self.valuePtr(old_loc).*;
                self.valuePtr(new_loc).* = old_value;
                self.deleteLocation(old_loc);
                return self.valuePtr(new_loc);
            }

            if (self.canUpdateKeyInPlace(old_loc, new_key)) {
                self.keyPtr(old_loc).* = new_key;
                return self.valuePtr(old_loc);
            }

            const old_value = self.valuePtr(old_loc).*;
            self.deleteAndReplace(old_loc);
            self.resetDetachedLocation(old_loc, new_key, old_value);
            self.insertNew(new_res, old_loc);
            return self.valuePtr(old_loc);
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
            const v = self.valuePtr(l).*;
            self.deleteLocation(l);
            return v;
        }

        // deleteAndReplace removes loc from the tree and moves a replacement node
        // into its place when needed. It updates min/max eagerly, reconnects parent
        // and child links, and starts rebalancing at the lowest node whose height
        // may have changed.
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

        // findReplacement chooses the node that will physically replace loc during
        // deletion. With two children it uses the in-order predecessor or successor
        // from the taller side, following Brown's optimized AVL deletion strategy.
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
                return Entry{
                    .Key = self.keyPtr(min).*,
                    .Value = self.valuePtr(min),
                };
            }
            return null;
        }

        // getMax returns the maximum element of the tree.
        // Time complexity: O(1).
        pub fn getMax(self: *Self) ?Entry {
            if (self.max) |max| {
                return Entry{
                    .Key = self.keyPtr(max).*,
                    .Value = self.valuePtr(max),
                };
            }
            return null;
        }

        // iteratorAtFirst returns an iterator positioned at the first element.
        // Time complexity: O(1).
        pub fn iteratorAtFirst(self: *Self) Iterator {
            return Iterator.init(self, self.min);
        }

        // iteratorAtLast returns an iterator positioned at the last element.
        // Time complexity: O(1).
        pub fn iteratorAtLast(self: *Self) Iterator {
            return Iterator.init(self, self.max);
        }

        // lowerBound returns an iterator positioned at the first element whose key is not less than k.
        // Time complexity: O(logn).
        pub fn lowerBound(self: *Self, k: K) Iterator {
            var loc = self.root;
            var candidate: ?Location = null;
            while (loc) |l| {
                switch (Comparer(k, self.keyPtr(l).*)) {
                    .lt => {
                        candidate = l;
                        loc = self.child(l, .left);
                    },
                    .eq => {
                        candidate = l;
                        loc = null;
                    },
                    .gt => {
                        loc = self.child(l, .right);
                    },
                }
            }
            return Iterator.init(self, candidate);
        }

        // upperBound returns an iterator positioned at the first element whose key is greater than k.
        // Time complexity: O(logn).
        pub fn upperBound(self: *Self, k: K) Iterator {
            var loc = self.root;
            var candidate: ?Location = null;
            while (loc) |l| {
                switch (Comparer(k, self.keyPtr(l).*)) {
                    .lt => {
                        candidate = l;
                        loc = self.child(l, .left);
                    },
                    .eq, .gt => {
                        loc = self.child(l, .right);
                    },
                }
            }
            return Iterator.init(self, candidate);
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
            if (comptime cacheCapabilities.hasOrderedStorage) {
                if (self.storage_ordered) {
                    return self.getInOrderedStorage(k);
                }
            }
            const res = self.locate(k);
            if (res.dir == .center) {
                if (res.loc) |loc| {
                    return self.valuePtr(loc);
                }
            }
            return null;
        }

        // getInOrderedStorage performs binary search on the dense storage prefix directly. It is
        // valid only while storage addresses follow key order.
        fn getInOrderedStorage(self: *Self, k: K) ?*V {
            var left: usize = 0;
            var right = self.length;
            while (left < right) {
                const mid = left + (right - left) / 2;
                const loc = self.lc.locationAt(mid);
                switch (Comparer(k, self.keyPtr(loc).*)) {
                    .lt => right = mid,
                    .eq => return self.valuePtr(loc),
                    .gt => left = mid + 1,
                }
            }
            return null;
        }

        // rank returns the position of k in the sorted sequence.
        // Returns null if k is not present.
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn rank(self: *Self, k: K) ?usize {
            if (!options.countChildren) {
                return self.rankLinearly(k);
            }

            return self.rankWithCountChildren(k);
        }

        // rankWithCountChildren uses cached left-subtree sizes to compute the rank
        // while descending the search path. Every time the search goes right, all
        // nodes in the left subtree plus the current node are known to come before k.
        fn rankWithCountChildren(self: *Self, k: K) ?usize {
            var loc = self.root;
            var result: usize = 0;
            while (loc) |l| {
                switch (Comparer(k, self.keyPtr(l).*)) {
                    .lt => {
                        loc = self.child(l, .left);
                    },
                    .gt => {
                        result += self.leftCount(l) + 1;
                        loc = self.child(l, .right);
                    },
                    .eq => {
                        return result + self.leftCount(l);
                    },
                }
            }
            return null;
        }

        // rankLinearly is the fallback used when countChildren is disabled. It
        // walks the sorted iterator until k is found or until the next key is
        // already greater than k.
        fn rankLinearly(self: *Self, k: K) ?usize {
            var it = self.iteratorAtFirst();
            var result: usize = 0;
            while (it.value()) |entry| {
                switch (Comparer(k, entry.Key)) {
                    .lt => return null,
                    .eq => return result,
                    .gt => {
                        result += 1;
                        it.next();
                    },
                }
            }
            return null;
        }

        // rankDistance returns the absolute distance between sorted positions of k1 and k2.
        // If k1 or k2 is not present in the tree, rankDistance returns null.
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn rankDistance(self: *Self, k1: K, k2: K) ?usize {
            const r1 = self.rank(k1) orelse return null;
            const r2 = self.rank(k2) orelse return null;
            return if (r2 >= r1) r2 - r1 else r1 - r2;
        }

        // countInRange returns the number of elements on the inclusive interval [k1, k2].
        // k1 and k2 themselves may not be present in the tree.
        // Example: [10 20 30 40 50 60], k1=15, k2=50 --> 4.
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn countInRange(self: *Self, k1: K, k2: K) usize {
            const r1 = self.lowerBoundRank(k1) orelse return 0;
            const r2 = self.floorRank(k2) orelse return 0;
            return if (r2 >= r1) r2 - r1 + 1 else 0;
        }

        // lowerBoundRank returns the rank of the first element whose key is >= k.
        fn lowerBoundRank(self: *Self, k: K) ?usize {
            if (options.countChildren) {
                return self.lowerBoundRankWithCountChildren(k);
            }
            return self.lowerBoundRankLinearly(k);
        }

        // floorRank returns the rank of the last element whose key is <= k.
        fn floorRank(self: *Self, k: K) ?usize {
            if (options.countChildren) {
                return self.floorRankWithCountChildren(k);
            }
            return self.floorRankLinearly(k);
        }

        // lowerBoundRankLinearly returns the rank of the first key >= k by scanning
        // in sorted order. It returns null when all keys are smaller than k.
        fn lowerBoundRankLinearly(self: *Self, k: K) ?usize {
            var it = self.iteratorAtFirst();
            var result: usize = 0;
            while (it.value()) |entry| {
                switch (Comparer(k, entry.Key)) {
                    .lt, .eq => return result,
                    .gt => {
                        result += 1;
                        it.next();
                    },
                }
            }
            return null;
        }

        // floorRankLinearly returns the rank of the last key <= k by scanning in
        // sorted order. It returns null when all keys are greater than k.
        fn floorRankLinearly(self: *Self, k: K) ?usize {
            var it = self.iteratorAtFirst();
            var result: usize = 0;
            if (self.len() == 0) {
                return null;
            }
            while (it.value()) |entry| {
                switch (Comparer(k, entry.Key)) {
                    .lt => return if (result == 0) null else result - 1,
                    .eq => return result,
                    .gt => {
                        result += 1;
                        it.next();
                    },
                }
            }
            return result - 1;
        }

        // floorRankWithCountChildren mirrors floorRankLinearly but uses cached
        // subtree sizes. candidate_rank tracks the best key <= k seen so far while
        // the search descends toward where k would be inserted.
        fn floorRankWithCountChildren(self: *Self, k: K) ?usize {
            var loc = self.root;
            var current_rank: usize = 0;
            var candidate_rank: usize = 0;
            if (self.len() == 0) {
                return null;
            }
            while (loc) |l| {
                switch (Comparer(k, self.keyPtr(l).*)) {
                    .lt => {
                        if (self.locEq(loc.?, self.min.?)) {
                            return null;
                        }
                        loc = self.child(l, .left);
                    },
                    .eq => return current_rank + self.leftCount(l),
                    .gt => {
                        candidate_rank = current_rank + self.leftCount(l);
                        current_rank += self.leftCount(l) + 1;
                        loc = self.child(l, .right);
                    },
                }
            }
            return candidate_rank;
        }

        // lowerBoundRankWithCountChildren returns the rank of the first key >= k.
        // current_rank is the number of nodes proven to be before the current
        // subtree, and candidate_rank stores the best possible lower bound found.
        fn lowerBoundRankWithCountChildren(self: *Self, k: K) ?usize {
            var loc = self.root;
            var current_rank: usize = 0;
            var candidate_rank: usize = 0;
            if (self.len() == 0) {
                return null;
            }
            while (loc) |l| {
                switch (Comparer(k, self.keyPtr(l).*)) {
                    .lt => {
                        loc = self.child(l, .left);
                        candidate_rank = current_rank + self.leftCount(l);
                    },
                    .eq => return current_rank + self.leftCount(l),
                    .gt => {
                        if (self.locEq(loc.?, self.max.?)) {
                            return null;
                        }
                        current_rank += self.leftCount(l) + 1;
                        loc = self.child(l, .right);
                    },
                }
            }
            return candidate_rank;
        }

        // at returns a an entry at the ith position of the sorted array.
        // Panics if position >= tree.Len().
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn at(self: *Self, pos: usize) Entry {
            const loc = self.locateAt(pos);
            return Entry{
                .Key = self.keyPtr(loc).*,
                .Value = self.valuePtr(loc),
            };
        }

        // iteratorAt returns an iterator positioned at the ith element.
        // Panics if position >= tree.Len().
        // Time complexity:
        //  O(logn) - if children node counts are enabled.
        //  O(n) - otherwise.
        pub fn iteratorAt(self: *Self, pos: usize) Iterator {
            const loc = self.locateAt(pos);
            return Iterator.init(self, loc);
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
            const kv = KV{
                .Key = self.keyPtr(loc).*,
                .Value = self.valuePtr(loc).*,
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

        // treeRotated reconnects a freshly rotated subtree to the old parent.
        // Rotation helpers only rearrange links inside the local subtree and return
        // its new root; this helper either attaches that root to oldRoot's parent
        // or promotes it to the tree root when the rotated subtree was the root.
        fn treeRotated(self: *Self, parent_loc: ?Location, oldRoot: Location, newRoot: Location) void {
            if (parent_loc) |p| {
                self.reparent(p, self.childDir(p, oldRoot), newRoot);
            } else {
                self.setRoot(newRoot);
            }
        }

        // checkBalance walks from loc toward the root, recalculating heights and
        // child counts and rotating the first unbalanced subtree it finds.
        //
        // When all_way_up is false, the walk stops once a node height does not
        // change: ancestors above it cannot become newly unbalanced. When it is
        // true, the walk continues to the root because the caller already knows
        // that ancestor counts/heights may need a full refresh after relinking.
        //
        // balance(l) == -2 means the left subtree is too tall. The child balance
        // chooses a single right rotation (rr) or a double left-right rotation (lr).
        // balance(l) == 2 mirrors that with right-left (rl) or single left (ll).
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

        // rr performs a single right rotation around l.
        //
        // Before:
        //
        //         l
        //        /
        //     left
        //     /  \
        //    A    B
        //
        // After:
        //
        //      left
        //      /  \
        //     A    l
        //         /
        //        B
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

        // lr performs a double left-right rotation around l.
        //
        // Before:
        //
        //          l
        //         /
        //      left
        //        \
        //      left_right
        //       /      \
        //      B        C
        //
        // After:
        //
        //      left_right
        //       /      \
        //    left       l
        //      \       /
        //       B     C
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

        // rl performs a double right-left rotation around l.
        //
        // Before:
        //
        //      l
        //       \
        //       right
        //       /
        //   right_left
        //    /      \
        //   B        C
        //
        // After:
        //
        //      right_left
        //       /      \
        //      l       right
        //       \      /
        //        B    C
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

        // ll performs a single left rotation around l.
        //
        // Before:
        //
        //      l
        //       \
        //       right
        //       /   \
        //      B     C
        //
        // After:
        //
        //       right
        //       /   \
        //      l     C
        //       \
        //        B
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
                switch (Comparer(k, self.keyPtr(l).*)) {
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

        // shouldLocateAtLinearly keeps near-edge lookups cheap. Even with subtree
        // counts enabled, taking a few iterator steps from min/max is simpler and
        // often faster than walking the tree by rank.
        fn shouldLocateAtLinearly(self: *Self, pos: usize) bool {
            const p = @min(pos, self.length - pos - 1);
            return p <= 8;
        }

        fn locateAtOrdered(self: *Self, pos: usize) Location {
            return self.lc.locationAt(pos);
        }

        fn nextIteratorLocation(self: *Self, loc: Location) ?Location {
            if (comptime cacheCapabilities.hasOrderedStorage) {
                if (self.storage_ordered) {
                    return self.lc.nextLocation(loc, self.length);
                }
            }
            return self.nextInOrderLocation(loc);
        }

        fn prevIteratorLocation(self: *Self, loc: Location) ?Location {
            if (comptime cacheCapabilities.hasOrderedStorage) {
                if (self.storage_ordered) {
                    return self.lc.prevLocation(loc);
                }
            }
            return self.prevInOrderLocation(loc);
        }

        fn locateAtLinearly(self: *Self, pos: usize) Location {
            if (pos < self.length / 2) {
                return self.advance(self.min.?, @as(isize, @intCast(pos)));
            }
            return self.advance(self.max.?, -@as(isize, @intCast(self.length - pos - 1)));
        }

        // locateAtByCount descends by comparing pos with left subtree sizes.
        fn locateAtByCount(self: *Self, pos: usize) Location {
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

        // locateAt returns the node at sorted position pos. Ordered address
        // storage can resolve the address directly; otherwise the tree uses
        // count-based descent when available and iterator-style movement when it
        // is cheaper or the tree was built without counts.
        fn locateAt(self: *Self, pos: usize) Location {
            if (pos >= self.len()) {
                @panic("index out of range");
            }
            if (comptime cacheCapabilities.hasOrderedStorage) {
                if (self.storage_ordered) {
                    return self.locateAtOrdered(pos);
                }
            }
            if (options.countChildren and !self.shouldLocateAtLinearly(pos)) {
                return self.locateAtByCount(pos);
            }
            return self.locateAtLinearly(pos);
        }
    };
}

fn i64Cmp(a: i64, b: i64) math.Order {
    return math.order(a, b);
}

const Pair = struct {
    first: i64,
    second: i64,
};

fn pairCmp(a: Pair, b: Pair) math.Order {
    return switch (math.order(a.first, b.first)) {
        .eq => math.order(a.second, b.second),
        else => |order| order,
    };
}

fn sortedRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return null,
            .eq => return idx,
            .gt => {},
        }
    }
    return null;
}

fn sortedLowerBoundRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt, .eq => return idx,
            .gt => {},
        }
    }
    return null;
}

fn sortedFloorRank(keys: []const i64, key: i64) ?usize {
    var result: ?usize = null;
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return result,
            .eq => return idx,
            .gt => result = idx,
        }
    }
    return result;
}

fn sortedUpperBoundRank(keys: []const i64, key: i64) ?usize {
    for (keys, 0..) |candidate, idx| {
        switch (i64Cmp(key, candidate)) {
            .lt => return idx,
            .eq, .gt => {},
        }
    }
    return null;
}

fn sortedCountInRange(keys: []const i64, k1: i64, k2: i64) usize {
    const r1 = sortedLowerBoundRank(keys, k1) orelse return 0;
    const r2 = sortedFloorRank(keys, k2) orelse return 0;
    return if (r2 >= r1) r2 - r1 + 1 else 0;
}

fn sortedRankDistance(keys: []const i64, k1: i64, k2: i64) ?usize {
    const r1 = sortedRank(keys, k1) orelse return null;
    const r2 = sortedRank(keys, k2) orelse return null;
    return if (r2 >= r1) r2 - r1 else r1 - r2;
}

fn expectOptionalEntryKey(comptime Entry: type, expected: ?i64, actual: ?Entry) !void {
    if (expected) |key| {
        try std.testing.expect(actual != null);
        try std.testing.expectEqual(key, actual.?.Key);
    } else {
        try std.testing.expectEqual(@as(?Entry, null), actual);
    }
}

test "empty tree" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    var it = t.iteratorAtFirst();
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    try std.testing.expect(t.delete(0) == null);
}

fn testTreeClear(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    t.clear();
    try std.testing.expectEqual(@as(usize, 0), t.len());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMin());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMax());

    for (0..128) |idx| {
        const key: i64 = @intCast(idx);
        const result = try t.insert(key, key);
        try std.testing.expect(result.inserted);
    }

    t.clear();
    try std.testing.expectEqual(@as(usize, 0), t.len());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMin());
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.getMax());
    try std.testing.expectEqual(@as(?*i64, null), t.get(64));
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.iteratorAtFirst().value());
    try std.testing.expectEqual(@as(?usize, null), t.rank(64));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(0, 127));

    const inserted = try t.insert(42, 100);
    try std.testing.expect(inserted.inserted);
    try std.testing.expectEqual(@as(usize, 1), t.len());
    try std.testing.expectEqual(@as(i64, 100), t.get(42).?.*);
    try std.testing.expectEqual(@as(?usize, 0), t.rank(42));
}

test "tree clear across options" {
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .PointerBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .PointerBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .ArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .StableArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testTreeClear(.{ .countChildren = false, .nodeCacheType = .SplitArrayBased });
    try testTreeClear(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

fn testTreeReclaimSearchable(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    for (0..16) |idx| {
        const key: i64 = @intCast(idx);
        _ = try t.insert(key, key * 10);
    }

    try std.testing.expectEqual(@as(i64, 10), t.delete(1).?);
    try std.testing.expectEqual(@as(i64, 30), t.delete(3).?);
    try std.testing.expectEqual(@as(i64, 60), t.delete(6).?);
    try std.testing.expectEqual(@as(i64, 70), t.delete(7).?);

    t.compactStorage();

    const expected = [_]i64{ 0, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15 };
    try std.testing.expectEqual(expected.len, t.len());
    try std.testing.expectEqual(@as(i64, 0), t.getMin().?.Key);
    try std.testing.expectEqual(@as(i64, 15), t.getMax().?.Key);
    try std.testing.expectEqual(@as(?usize, 4), t.rank(8));
    try std.testing.expectEqual(@as(usize, 4), t.countInRange(8, 11));

    var it = t.iteratorAtFirst();
    for (expected) |key| {
        const entry = it.value() orelse return error.MissingEntry;
        try std.testing.expectEqual(key, entry.Key);
        try std.testing.expectEqual(key * 10, entry.Value.*);
        it.next();
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());
}

test "tree compactStorage keeps compacting caches searchable" {
    try testTreeReclaimSearchable(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testTreeReclaimSearchable(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testTreeReclaimSearchable(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

fn testTreeCompactStorageNoop(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(2, 20);
    _ = try t.insert(1, 10);
    _ = try t.insert(3, 30);

    t.compactStorage();

    try std.testing.expectEqual(@as(usize, 3), t.len());
    try std.testing.expectEqual(@as(i64, 1), t.getMin().?.Key);
    try std.testing.expectEqual(@as(i64, 3), t.getMax().?.Key);
    try std.testing.expectEqual(@as(i64, 20), t.get(2).?.*);
}

test "tree compactStorage is noop for pointer cache" {
    try testTreeCompactStorageNoop(.{ .nodeCacheType = .PointerBased });
}

fn testTreeOrderStorageByKey(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    const inserted_keys = [_]i64{ 8, 3, 12, 1, 6, 10, 14, 0, 2, 5, 7, 9, 11, 13, 15, 4 };
    for (inserted_keys) |key| {
        _ = try t.insert(key, key * 10);
    }

    try std.testing.expectEqual(@as(i64, 10), t.delete(1).?);
    try std.testing.expectEqual(@as(i64, 60), t.delete(6).?);
    try std.testing.expectEqual(@as(i64, 120), t.delete(12).?);
    try std.testing.expectEqual(@as(i64, 140), t.delete(14).?);

    t.orderStorageByKey();

    const expected = [_]i64{ 0, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15 };
    try std.testing.expectEqual(expected.len, t.len());
    try std.testing.expectEqual(@as(usize, expected.len), t.lc.slotsLen());
    try std.testing.expectEqual(@as(usize, 0), t.lc.freeCount());
    try std.testing.expectEqual(@TypeOf(t.lc).InvalidAddr, t.lc.freeHead());

    for (expected, 0..) |key, idx| {
        try std.testing.expectEqual(key, t.lc.keyPtr(t.lc.locationAt(idx)).*);
        try std.testing.expectEqual(key, t.at(idx).Key);
        try std.testing.expectEqual(key, t.iteratorAt(idx).value().?.Key);
    }

    var it = t.iteratorAtFirst();
    for (expected) |key| {
        try std.testing.expectEqual(key, it.value().?.Key);
        it.next();
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.iteratorAtLast();
    var rev_idx = expected.len;
    while (rev_idx > 0) {
        rev_idx -= 1;
        try std.testing.expectEqual(expected[rev_idx], it.value().?.Key);
        it.prev();
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    try std.testing.expectEqual(@as(i64, 0), t.getMin().?.Key);
    try std.testing.expectEqual(@as(i64, 15), t.getMax().?.Key);
    try std.testing.expectEqual(@as(i64, 100), t.get(10).?.*);
    try std.testing.expectEqual(@as(?*i64, null), t.get(6));

    const deleted = t.deleteAt(4);
    try std.testing.expectEqual(@as(i64, 5), deleted.Key);
    try std.testing.expectEqual(@as(i64, 50), deleted.Value);
    try std.testing.expectEqual(@as(?usize, null), t.rank(5));
}

test "tree orderStorageByKey orders address caches by sorted key" {
    try testTreeOrderStorageByKey(.{ .countChildren = false, .nodeCacheType = .ArrayBased });
    try testTreeOrderStorageByKey(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testTreeOrderStorageByKey(.{ .countChildren = false, .nodeCacheType = .StableArrayBased });
    try testTreeOrderStorageByKey(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testTreeOrderStorageByKey(.{ .countChildren = false, .nodeCacheType = .SplitArrayBased });
    try testTreeOrderStorageByKey(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

test "tree orderStorageByKey is noop for pointer cache" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .nodeCacheType = .PointerBased });
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(2, 20);
    _ = try t.insert(1, 10);
    _ = try t.insert(3, 30);

    t.orderStorageByKey();

    try std.testing.expectEqual(@as(usize, 3), t.len());
    try std.testing.expectEqual(@as(i64, 1), t.at(0).Key);
    try std.testing.expectEqual(@as(i64, 2), t.at(1).Key);
    try std.testing.expectEqual(@as(i64, 3), t.at(2).Key);
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

fn testTreeUpdateKey(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        _ = try t.insert(1, 10);
        try std.testing.expectEqual(@as(?*i64, null), t.updateKey(2, 3));
        try std.testing.expectEqual(@as(usize, 1), t.len());
        try std.testing.expectEqual(@as(i64, 10), t.get(1).?.*);
        try checkHeightAndBalance(&t);
    }

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        _ = try t.insert(1, 10);
        const v = t.updateKey(1, 1).?;
        try std.testing.expectEqual(@as(i64, 10), v.*);
        try std.testing.expectEqual(@as(usize, 1), t.len());
        try std.testing.expectEqual(@as(i64, 10), t.get(1).?.*);
        try checkHeightAndBalance(&t);
    }

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        _ = try t.insert(1, 10);
        _ = try t.insert(2, 20);
        const v = t.updateKey(1, 2).?;
        try std.testing.expectEqual(@as(i64, 10), v.*);
        try std.testing.expectEqual(@as(usize, 1), t.len());
        try std.testing.expectEqual(@as(?*i64, null), t.get(1));
        try std.testing.expectEqual(@as(i64, 10), t.get(2).?.*);
        try checkHeightAndBalance(&t);
    }

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        _ = try t.insert(1, 10);
        _ = try t.insert(3, 30);
        _ = try t.insert(5, 50);
        const v = t.updateKey(3, 4).?;
        try std.testing.expectEqual(@as(i64, 30), v.*);
        try std.testing.expectEqual(@as(usize, 3), t.len());
        try std.testing.expectEqual(@as(?*i64, null), t.get(3));
        try std.testing.expectEqual(@as(i64, 30), t.get(4).?.*);
        try std.testing.expectEqual(@as(i64, 1), t.getMin().?.Key);
        try std.testing.expectEqual(@as(i64, 5), t.getMax().?.Key);
        try checkHeightAndBalance(&t);
    }

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        var i: i64 = 1;
        while (i <= 8) : (i += 1) {
            _ = try t.insert(i, i * 10);
        }
        const v = t.updateKey(2, 9).?;
        try std.testing.expectEqual(@as(i64, 20), v.*);
        try std.testing.expectEqual(@as(usize, 8), t.len());
        try std.testing.expectEqual(@as(?*i64, null), t.get(2));
        try std.testing.expectEqual(@as(i64, 20), t.get(9).?.*);
        try std.testing.expectEqual(@as(i64, 1), t.getMin().?.Key);
        try std.testing.expectEqual(@as(i64, 9), t.getMax().?.Key);
        try checkHeightAndBalance(&t);

        var it = t.iteratorAtFirst();
        var prev: ?i64 = null;
        while (it.value()) |entry| {
            if (prev) |p| {
                try std.testing.expect(p < entry.Key);
            }
            prev = entry.Key;
            it.next();
        }
    }

    {
        var t = try TreeType.init(a);
        defer t.deinit();
        var keys: [128]i64 = undefined;
        for (&keys, 0..) |*key, idx| {
            key.* = @intCast(idx);
            _ = try t.insert(key.*, key.* * 10);
        }
        var r = std.Random.DefaultPrng.init(1);
        r.random().shuffle(i64, &keys);

        for (keys) |key| {
            const new_key = key + 1024;
            const v = t.updateKey(key, new_key).?;
            try std.testing.expectEqual(key * 10, v.*);
            try std.testing.expectEqual(@as(?*i64, null), t.get(key));
            try std.testing.expectEqual(key * 10, t.get(new_key).?.*);
            try checkHeightAndBalance(&t);
        }

        var it = t.iteratorAtFirst();
        var prev: ?i64 = null;
        var count: usize = 0;
        while (it.value()) |entry| {
            if (prev) |p| {
                try std.testing.expect(p < entry.Key);
            }
            prev = entry.Key;
            count += 1;
            it.next();
        }
        try std.testing.expectEqual(@as(usize, keys.len), count);
    }
}

test "tree updateKey (pointer cache)" {
    try testTreeUpdateKey(.{ .countChildren = true, .nodeCacheType = .PointerBased });
}

test "tree updateKey (array cache)" {
    try testTreeUpdateKey(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
}

test "stable array based value pointers survive cache growth" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .nodeCacheType = .StableArrayBased });
    var t = try TreeType.init(a);
    defer t.deinit();

    const first = (try t.insert(0, 42)).v;
    for (1..4096) |idx| {
        const key: i64 = @intCast(idx);
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(i64, 42), first.*);
    first.* = 99;
    try std.testing.expectEqual(@as(i64, 99), t.get(0).?.*);
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
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = false });
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

fn testTreeRank(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    for ([_]i64{ 30, 10, 50, 20, 40 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(?usize, 0), t.rank(10));
    try std.testing.expectEqual(@as(?usize, 1), t.rank(20));
    try std.testing.expectEqual(@as(?usize, 2), t.rank(30));
    try std.testing.expectEqual(@as(?usize, 3), t.rank(40));
    try std.testing.expectEqual(@as(?usize, 4), t.rank(50));

    try std.testing.expectEqual(@as(?usize, null), t.rank(5));
    try std.testing.expectEqual(@as(?usize, null), t.rank(25));
    try std.testing.expectEqual(@as(?usize, null), t.rank(60));
}

test "tree rank with countChildren" {
    try testTreeRank(.{ .countChildren = true });
}

test "tree rank without countChildren" {
    try testTreeRank(.{ .countChildren = false });
}

fn testCountInRange(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    for ([_]i64{ 30, 10, 50, 20, 40 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(usize, 0), t.countInRange(1, 2));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(2, 1));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(51, 52));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(52, 51));
    try std.testing.expectEqual(@as(usize, 1), t.countInRange(10, 10));
    try std.testing.expectEqual(@as(usize, 2), t.countInRange(10, 20));
    try std.testing.expectEqual(@as(usize, 3), t.countInRange(10, 30));
    try std.testing.expectEqual(@as(usize, 4), t.countInRange(10, 40));
    try std.testing.expectEqual(@as(usize, 1), t.countInRange(9, 10));
    try std.testing.expectEqual(@as(usize, 1), t.countInRange(10, 10));
    try std.testing.expectEqual(@as(usize, 3), t.countInRange(9, 30));
    try std.testing.expectEqual(@as(usize, 3), t.countInRange(9, 31));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(31, 9));
    try std.testing.expectEqual(@as(usize, 5), t.countInRange(9, 100));
    try std.testing.expectEqual(@as(usize, 5), t.countInRange(10, 50));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(11, 19));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(21, 29));
    try std.testing.expectEqual(@as(usize, 1), t.countInRange(50, 50));
    try std.testing.expectEqual(@as(usize, 1), t.countInRange(50, 60));
    try std.testing.expectEqual(@as(usize, 0), t.countInRange(20, 10));
}

test "tree countInRange without countChildren" {
    try testCountInRange(.{ .countChildren = false });
}

test "tree countInRange with countChildren" {
    try testCountInRange(.{ .countChildren = true });
}

fn testTreeRankDistance(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    for ([_]i64{ 30, 10, 50, 20, 40 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(?usize, 0), t.rankDistance(10, 10));
    try std.testing.expectEqual(@as(?usize, 1), t.rankDistance(10, 20));
    try std.testing.expectEqual(@as(?usize, 2), t.rankDistance(20, 40));
    try std.testing.expectEqual(@as(?usize, 3), t.rankDistance(10, 40));
    try std.testing.expectEqual(@as(?usize, 4), t.rankDistance(10, 50));
    try std.testing.expectEqual(@as(?usize, 4), t.rankDistance(50, 10));

    try std.testing.expectEqual(@as(?usize, null), t.rankDistance(5, 10));
    try std.testing.expectEqual(@as(?usize, null), t.rankDistance(10, 5));
    try std.testing.expectEqual(@as(?usize, null), t.rankDistance(5, 60));
}

test "tree rankDistance with countChildren" {
    try testTreeRankDistance(.{ .countChildren = true });
}

test "tree rankDistance without countChildren" {
    try testTreeRankDistance(.{ .countChildren = false });
}

fn testRankRangeAndBoundsAgainstSortedSlice(comptime options: Options) !void {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, options);
    var t = try TreeType.init(a);
    defer t.deinit();

    const sorted_keys = [_]i64{ -50, -10, 0, 3, 4, 10, 17, 31, 32, 99 };
    var insert_keys = sorted_keys;

    var prng = std.Random.DefaultPrng.init(0x5eed);
    prng.random().shuffle(i64, insert_keys[0..]);

    for (insert_keys) |key| {
        const result = try t.insert(key, key);
        try std.testing.expect(result.inserted);
    }

    for (sorted_keys, 0..) |key, idx| {
        try std.testing.expectEqual(@as(?usize, idx), t.rank(key));
        try std.testing.expectEqual(key, t.at(idx).Key);
        try std.testing.expectEqual(key, t.iteratorAt(idx).value().?.Key);
    }

    const query_keys = [_]i64{
        -60, -50, -49, -11, -10, -9, -1, 0,  1,  3,  4,   5,
        10,  16,  17,  18,  30,  31, 32, 33, 98, 99, 100,
    };

    for (query_keys) |key| {
        const lower_rank = sortedLowerBoundRank(&sorted_keys, key);
        const lower_key = if (lower_rank) |rank| sorted_keys[rank] else null;
        try expectOptionalEntryKey(TreeType.Entry, lower_key, t.lowerBound(key).value());

        const upper_rank = sortedUpperBoundRank(&sorted_keys, key);
        const upper_key = if (upper_rank) |rank| sorted_keys[rank] else null;
        try expectOptionalEntryKey(TreeType.Entry, upper_key, t.upperBound(key).value());

        try std.testing.expectEqual(sortedRank(&sorted_keys, key), t.rank(key));
    }

    for (query_keys) |k1| {
        for (query_keys) |k2| {
            try std.testing.expectEqual(sortedCountInRange(&sorted_keys, k1, k2), t.countInRange(k1, k2));
            try std.testing.expectEqual(sortedRankDistance(&sorted_keys, k1, k2), t.rankDistance(k1, k2));
        }
    }
}

test "tree rank range and bounds match sorted slice across options" {
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = false, .nodeCacheType = .PointerBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = true, .nodeCacheType = .PointerBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = false, .nodeCacheType = .ArrayBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = false, .nodeCacheType = .StableArrayBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = true, .nodeCacheType = .StableArrayBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = false, .nodeCacheType = .SplitArrayBased });
    try testRankRangeAndBoundsAgainstSortedSlice(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

test "tree floorRankWithCountChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    try std.testing.expectEqual(@as(?usize, null), t.floorRankWithCountChildren(9));

    for ([_]i64{ 30, 10, 50, 20, 40, 60, 70, 80 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(?usize, 0), t.floorRankWithCountChildren(10));
    try std.testing.expectEqual(@as(?usize, 3), t.floorRankWithCountChildren(40));
    try std.testing.expectEqual(@as(?usize, 4), t.floorRankWithCountChildren(50));
    try std.testing.expectEqual(@as(?usize, 4), t.floorRankWithCountChildren(51));
    try std.testing.expectEqual(@as(?usize, null), t.floorRankWithCountChildren(9));
    try std.testing.expectEqual(@as(?usize, 0), t.floorRankWithCountChildren(11));
    try std.testing.expectEqual(@as(?usize, 2), t.floorRankWithCountChildren(39));
    try std.testing.expectEqual(@as(?usize, 7), t.floorRankWithCountChildren(80));
    try std.testing.expectEqual(@as(?usize, 7), t.floorRankWithCountChildren(81));
}

test "tree lowerBoundRankWithCountChildren" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    try std.testing.expectEqual(@as(?usize, null), t.lowerBoundRankWithCountChildren(9));

    for ([_]i64{ 30, 10, 50, 20, 40, 60, 70, 80 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(?usize, 0), t.lowerBoundRankWithCountChildren(10));
    try std.testing.expectEqual(@as(?usize, 3), t.lowerBoundRankWithCountChildren(40));
    try std.testing.expectEqual(@as(?usize, 4), t.lowerBoundRankWithCountChildren(50));
    try std.testing.expectEqual(@as(?usize, 5), t.lowerBoundRankWithCountChildren(51));
    try std.testing.expectEqual(@as(?usize, null), t.lowerBoundRankWithCountChildren(90));
    try std.testing.expectEqual(@as(?usize, 1), t.lowerBoundRankWithCountChildren(11));
    try std.testing.expectEqual(@as(?usize, 3), t.lowerBoundRankWithCountChildren(39));
    try std.testing.expectEqual(@as(?usize, 7), t.lowerBoundRankWithCountChildren(80));
    try std.testing.expectEqual(@as(?usize, null), t.lowerBoundRankWithCountChildren(81));
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
    var it = t.iteratorAtFirst();
    i = 0;
    while (i < 128) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.next();
        i += 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.iteratorAtLast();
    i = 127;
    while (i >= 0) {
        const e = it.value();
        try std.testing.expectEqual(i, e.?.Key);
        try std.testing.expectEqual(i, e.?.Value.*);
        it.prev();
        i -= 1;
    }
    try std.testing.expectEqual(@as(?TreeType.Entry, null), it.value());

    it = t.iteratorAtFirst();
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

    it = t.iteratorAtFirst();
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

test "tree iteratorAt" {
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
        var it = t.iteratorAt(@as(usize, @intCast(i)));
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
        it = t.iteratorAt(@as(usize, @intCast(i)));
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

test "tree bounds" {
    const a = std.testing.allocator;
    const TreeType = TreeWithOptions(i64, i64, i64Cmp, .{ .countChildren = true });
    var t = try TreeType.init(a);
    defer t.deinit();

    for ([_]i64{ 0, 10, 20, 30, 40 }) |key| {
        _ = try t.insert(key, key);
    }

    try std.testing.expectEqual(@as(i64, 10), t.lowerBound(5).value().?.Key);
    try std.testing.expectEqual(@as(i64, 10), t.lowerBound(10).value().?.Key);
    try std.testing.expectEqual(@as(i64, 20), t.lowerBound(20).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.lowerBound(25).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.lowerBound(30).value().?.Key);
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.lowerBound(41).value());

    try std.testing.expectEqual(@as(i64, 10), t.upperBound(5).value().?.Key);
    try std.testing.expectEqual(@as(i64, 20), t.upperBound(10).value().?.Key);
    try std.testing.expectEqual(@as(i64, 30), t.upperBound(20).value().?.Key);
    try std.testing.expectEqual(@as(?TreeType.Entry, null), t.upperBound(40).value());
}

test "tree bounds with composite keys" {
    const a = std.testing.allocator;
    const TreeType = Tree(Pair, i64, pairCmp);
    var t = try TreeType.init(a);
    defer t.deinit();

    _ = try t.insert(.{ .first = 10, .second = 10 }, 10);
    _ = try t.insert(.{ .first = 20, .second = 20 }, 20);
    _ = try t.insert(.{ .first = 20, .second = 30 }, 30);
    _ = try t.insert(.{ .first = 30, .second = 40 }, 40);

    try std.testing.expectEqual(Pair{ .first = 20, .second = 20 }, t.lowerBound(.{ .first = 20, .second = 0 }).value().?.Key);
    try std.testing.expectEqual(Pair{ .first = 20, .second = 20 }, t.lowerBound(.{ .first = 20, .second = 20 }).value().?.Key);
    try std.testing.expectEqual(Pair{ .first = 30, .second = 40 }, t.upperBound(.{ .first = 20, .second = 30 }).value().?.Key);
    try std.testing.expectEqual(@as(?usize, 1), t.rank(.{ .first = 20, .second = 20 }));
    try std.testing.expectEqual(@as(?usize, 2), t.rank(.{ .first = 20, .second = 30 }));
    try std.testing.expectEqual(@as(?usize, null), t.rank(.{ .first = 20, .second = 25 }));
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

test "tree random (array cache)" {
    try testTreeRandom(.{ .countChildren = true, .nodeCacheType = .ArrayBased });
}

test "tree random (split array cache)" {
    try testTreeRandom(.{ .countChildren = true, .nodeCacheType = .SplitArrayBased });
}

fn TestLocationCache(comptime underlying: type) type {
    return struct {
        const Self = @This();
        pub const Location = underlying.Location;
        pub const Meta = underlying.Meta;

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

        pub fn keyPtr(self: *Self, loc: Location) *i64 {
            return self.u.keyPtr(loc);
        }

        pub fn valuePtr(self: *Self, loc: Location) *i64 {
            return self.u.valuePtr(loc);
        }

        pub fn meta(self: *Self, loc: Location) Meta {
            return self.u.meta(loc);
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

fn testFastDeinit(
    io: InitOptions,
    a: std.mem.Allocator,
) !void {
    const cacheType = cache.Create(.PointerBased, i64, i64, struct {});
    const TreeType = InitTreeType(i64, i64, TestLocationCache(cacheType), i64Cmp, .{});
    var t = try TreeType.initWithOptions(a, io);
    defer t.deinit();
    t.lc.destroyHook = struct {
        fn doPanic(_: cacheType.Location) void {
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
    try testFastDeinit(.{ .allowFastDeinit = .auto }, arena.allocator());
}

test "arena allocator: always fast deinit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try testFastDeinit(.{ .allowFastDeinit = .always }, arena.allocator());
}

test "fixed buffer allocator: auto fast deinit" {
    var buff: [16 * 1024]u8 = undefined;
    var fb = std.heap.FixedBufferAllocator.init(&buff);
    try testFastDeinit(.{ .allowFastDeinit = .auto }, fb.allocator());
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
    try std.testing.expectEqual(result.height, tree.meta(l).height.*);
    if (tree.balance(l) < -1 or tree.balance(l) > 1) {
        return error{
            InvalidBalance,
        }.InvalidBalance;
    }
    return result;
}
