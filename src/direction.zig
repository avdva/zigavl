// direction represents a parent-child relation for Get(Find) operation.
// - .left means that the child is a left child of the parent.
// - .right means that the child is a right child of the parent.
// - .center means that node's key matches given key.
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
