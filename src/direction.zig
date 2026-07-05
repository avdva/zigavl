pub const direction = enum {
    left,
    center,
    right,

    pub fn invert(self: direction) direction {
        switch (self) {
            .left => return .right,
            .right => return .left,
            .center => return .center,
        }
    }
};
