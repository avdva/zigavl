pub fn makeDataType(comptime K: type, comptime V: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        k: K = undefined,
        v: V = undefined,
        tags: Tags = undefined,
        h: u8 = 0,

        pub fn setHeight(self: *Self, h: u8) bool {
            const old = self.h;
            self.h = h;
            return old != h;
        }
    };
}
