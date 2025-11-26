pub fn MakeNodeDataType(comptime K: type, comptime V: type, comptime Tags: type) type {
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

pub fn MakeNodeType(comptime K: type, comptime V: type, comptime L: type, comptime Tags: type) type {
    return struct {
        const Self = @This();
        pub const NodeData = MakeNodeDataType(K, V, Tags);

        data: NodeData,
        left: ?L,
        right: ?L,
        parent: ?L,

        pub fn init() Self {
            return Self{
                .data = NodeData{},
                .left = null,
                .right = null,
                .parent = null,
            };
        }
    };
}