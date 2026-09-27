const std = @import("std");

// findIndex returns the dense storage index whose key compares equal to key.
pub fn findIndex(cache: anytype, length: usize, key: anytype, comptime compare: anytype) ?usize {
    var left: usize = 0;
    var right = length;
    while (left < right) {
        const mid = left + (right - left) / 2;
        const loc = cache.locationAt(mid);
        switch (compare(key, cache.keyPtr(loc).*)) {
            .lt => right = mid,
            .eq => return mid,
            .gt => left = mid + 1,
        }
    }
    return null;
}

// lowerBoundIndex returns the first dense storage index whose key is >= key,
// or length when every stored key is smaller.
pub fn lowerBoundIndex(cache: anytype, length: usize, key: anytype, comptime compare: anytype) usize {
    var left: usize = 0;
    var right = length;
    while (left < right) {
        const mid = left + (right - left) / 2;
        const loc = cache.locationAt(mid);
        switch (compare(key, cache.keyPtr(loc).*)) {
            .lt, .eq => right = mid,
            .gt => left = mid + 1,
        }
    }
    return left;
}

// upperBoundIndex returns the first dense storage index whose key is > key,
// or length when no greater stored key exists.
pub fn upperBoundIndex(cache: anytype, length: usize, key: anytype, comptime compare: anytype) usize {
    var left: usize = 0;
    var right = length;
    while (left < right) {
        const mid = left + (right - left) / 2;
        const loc = cache.locationAt(mid);
        switch (compare(key, cache.keyPtr(loc).*)) {
            .lt => right = mid,
            .eq, .gt => left = mid + 1,
        }
    }
    return left;
}

fn i64Cmp(a: i64, b: i64) std.math.Order {
    return std.math.order(a, b);
}

test "ordered search indices" {
    const Cache = struct {
        keys: []i64,

        fn locationAt(_: *@This(), pos: usize) usize {
            return pos;
        }

        fn keyPtr(self: *@This(), pos: usize) *i64 {
            return &self.keys[pos];
        }
    };

    var keys = [_]i64{ 10, 20, 30, 40 };
    var cache = Cache{ .keys = &keys };

    try std.testing.expectEqual(@as(?usize, null), findIndex(&cache, 0, 10, i64Cmp));
    try std.testing.expectEqual(@as(usize, 0), lowerBoundIndex(&cache, 0, 10, i64Cmp));
    try std.testing.expectEqual(@as(usize, 0), upperBoundIndex(&cache, 0, 10, i64Cmp));

    try std.testing.expectEqual(@as(?usize, null), findIndex(&cache, keys.len, 5, i64Cmp));
    try std.testing.expectEqual(@as(?usize, 2), findIndex(&cache, keys.len, 30, i64Cmp));
    try std.testing.expectEqual(@as(?usize, null), findIndex(&cache, keys.len, 50, i64Cmp));

    try std.testing.expectEqual(@as(usize, 0), lowerBoundIndex(&cache, keys.len, 5, i64Cmp));
    try std.testing.expectEqual(@as(usize, 1), lowerBoundIndex(&cache, keys.len, 20, i64Cmp));
    try std.testing.expectEqual(@as(usize, 2), lowerBoundIndex(&cache, keys.len, 25, i64Cmp));
    try std.testing.expectEqual(@as(usize, 4), lowerBoundIndex(&cache, keys.len, 50, i64Cmp));

    try std.testing.expectEqual(@as(usize, 0), upperBoundIndex(&cache, keys.len, 5, i64Cmp));
    try std.testing.expectEqual(@as(usize, 2), upperBoundIndex(&cache, keys.len, 20, i64Cmp));
    try std.testing.expectEqual(@as(usize, 2), upperBoundIndex(&cache, keys.len, 25, i64Cmp));
    try std.testing.expectEqual(@as(usize, 4), upperBoundIndex(&cache, keys.len, 50, i64Cmp));
}
