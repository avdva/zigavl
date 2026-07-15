// MakeDataType returns a type that represents a data node of the tree.
// It contains Key, Value, Height, and (possibly empty) Tags.
pub fn MakeDataType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        k: K = undefined,
        v: V = undefined,
        tags: Tags = undefined,
        h: u8 = 0,

        // setHeight sets node's height, returning true, if it was different.
        pub fn setHeight(self: *Self, h: u8) bool {
            const old = self.h;
            self.h = h;
            return old != h;
        }
    };
}
