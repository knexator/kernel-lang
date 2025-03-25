const sample_vau_program =
    \\ ($define! factorial ($lambda (n) ($if (=? n 0) 1 (* n (factorial (- n 1))))))
    \\ (print (factorial 3))
;

test "$define!" {
    try testHelper(std.testing.allocator,
        \\ ($define! a 10)
        \\ a
    , "10");
}

pub fn testHelper(gpa: std.mem.Allocator, source: []const u8, expected_raw: []const u8) !void {
    var bank = Sexpr.Bank.init(gpa);
    defer bank.deinit();
    const expected = blk: {
        var parser: Parser = .{ .remaining_text = expected_raw };
        const result = (try parser.next(&bank)).?;
        try std.testing.expect(try parser.next(&bank) == null);
        break :blk result;
    };
    var parser: Parser = .{ .remaining_text = source };
    var env = Sexpr.builtin.nil;
    var last_value = Sexpr.builtin.@"#inert";
    while (parser.next(&bank) catch @panic("bad text")) |v| {
        last_value = eval(v, &env, &bank);
    }
    try std.testing.expect(last_value.equals(expected));
}

pub fn main() !void {
    var debug_allocator: std.heap.DebugAllocator(.{}) = .init;
    const gpa, const is_debug = gpa: {
        if (builtin.os.tag == .wasi) break :gpa .{ std.heap.wasm_allocator, false };
        break :gpa switch (builtin.mode) {
            .Debug, .ReleaseSafe => .{ debug_allocator.allocator(), true },
            .ReleaseFast, .ReleaseSmall => .{ std.heap.smp_allocator, false },
        };
    };
    defer if (is_debug) {
        _ = debug_allocator.deinit();
    };

    const stdout_file = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_file);
    const stdout = bw.writer();
    defer bw.flush() catch std.log.err("Failed to flush stdout", .{});

    // TODO: REPL

    var bank = Sexpr.Bank.init(gpa);
    defer bank.deinit();
    var parser: Parser = .{ .remaining_text = 
        \\ ($define! a 10) 
        \\ a
    };

    var env = Sexpr.builtin.nil;

    while (try parser.next(&bank)) |v| {
        try stdout.print("read: {any}\n", .{v});
        try stdout.print("eval'd: {any}\n", .{eval(v, &env, &bank)});
    }
}

fn lookup(key: *const Sexpr, env: *const Sexpr) ?*const Sexpr {
    assert(key.is(.atom));

    // self evaluating symbols
    if (isNumber(key.atom.value)) return key;

    var remaining_list = env;
    while (remaining_list.is(.pair)) {
        const entry = remaining_list.pair.left;
        assert(entry.is(.pair));
        assert(entry.pair.left.is(.atom));
        if (entry.pair.left.atom.equals(key.atom)) {
            return entry.pair.right;
        }
    }
    assert(remaining_list.equals(Sexpr.builtin.nil));
    return null;
}

fn eval(expr: *const Sexpr, env: **const Sexpr, bank: *Sexpr.Bank) *const Sexpr {
    switch (expr.*) {
        .atom => return lookup(expr, env.*) orelse @panic("unbound variable"),
        .pair => |pair| {
            if (pair.left.equals(&.{ .atom = .{ .value = "$define!" } })) {
                const name = pair.right.pair.left;
                const value = pair.right.pair.right.pair.left;
                env.* = bank.doPair(bank.doPair(name, value), env.*);
                return Sexpr.builtin.@"#inert";
            } else {
                unreachable;
            }
        },
    }
}

pub const Atom = struct {
    value: []const u8,

    pub fn equals(this: Atom, other: Atom) bool {
        return std.mem.eql(u8, this.value, other.value);
    }
};
pub const Pair = struct {
    left: *const Sexpr,
    right: *const Sexpr,

    pub fn equals(this: Pair, other: Pair) bool {
        return this.left.equals(other.left) and this.right.equals(other.right);
    }
};
pub const Sexpr = union(enum) {
    atom: Atom,
    pair: Pair,

    pub const Address = struct {
        value: []const Item,

        pub const Item = enum { left, right };

        pub fn equals(this: Address, other: Address) bool {
            return std.mem.eql(Item, this.value, other.value);
        }
    };

    pub const Bank = struct {
        pool: std.heap.MemoryPool(Sexpr),
        pub fn init(allocator: std.mem.Allocator) Bank {
            return .{ .pool = .init(allocator) };
        }
        pub fn deinit(self: *Bank) void {
            self.pool.deinit();
        }

        pub fn doAtom(self: *Bank, value: []const u8) !*const Sexpr {
            const res = self.pool.create() catch @panic("OoM");
            res.* = .{ .atom = .{ .value = value } };
            return res;
        }

        pub fn doPair(self: *Bank, left: *const Sexpr, right: *const Sexpr) *const Sexpr {
            const res = self.pool.create() catch @panic("OoM");
            res.* = .{ .pair = .{ .left = left, .right = right } };
            return res;
        }
    };

    pub const builtin: struct {
        nil: *const Sexpr = &.{ .atom = .{ .value = "nil" } },
        @"#inert": *const Sexpr = &.{ .atom = .{ .value = "#inert" } },
        true: *const Sexpr = &.{ .atom = .{ .value = "true" } },
        false: *const Sexpr = &.{ .atom = .{ .value = "false" } },
    } = .{};

    pub fn equals(this: *const Sexpr, other: *const Sexpr) bool {
        if (this == other) return true;
        if (std.meta.activeTag(this.*) != std.meta.activeTag(other.*)) return false;
        return switch (this.*) {
            .atom => |this_atom| this_atom.equals(other.atom),
            .pair => |this_pair| this_pair.equals(other.pair),
        };
    }

    pub fn is(this: *const Sexpr, kind: std.meta.FieldEnum(Sexpr)) bool {
        return std.meta.activeTag(this.*) == kind;
    }

    pub fn getAt(this: *const Sexpr, address: Address) ?*const Sexpr {
        var res = this;
        for (address) |item| {
            res = switch (res.*) {
                .pair => |p| switch (item) {
                    .left => p.left,
                    .right => p.right,
                },
                else => return null,
            };
        }
        return res;
    }

    pub fn setAt(this: *const Sexpr, mem: *Bank, address: Address, value: *const Sexpr) !*const Sexpr {
        if (address.len == 0) {
            return value;
        } else {
            const first = address[0];
            const rest = address[1..];
            switch (this.*) {
                .pair => |p| {
                    switch (first) {
                        .left => {
                            const new_left = try p.left.setAt(mem, rest, value);
                            return mem.storeSexpr(Sexpr.doPair(new_left, p.right));
                        },
                        .right => {
                            const new_right = try p.right.setAt(mem, rest, value);
                            return mem.storeSexpr(Sexpr.doPair(p.left, new_right));
                        },
                    }
                },
                else => return error.SetAtInvalidAddress,
            }
        }
    }

    pub fn format(value: *const Sexpr, comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: std.io.AnyWriter) !void {
        assert(std.mem.eql(u8, fmt, ""));
        assert(std.meta.eql(options, .{}));
        switch (value.*) {
            .atom => |a| try writer.writeAll(a.value),
            .pair => |p| {
                try writer.writeAll("(");
                try p.left.format("", options, writer);
                var rest = p.right;
                while (rest.is(.pair)) {
                    try writer.writeAll(" ");
                    try rest.pair.left.format("", options, writer);
                    rest = rest.pair.right;
                }
                if (!rest.equals(Sexpr.builtin.nil)) {
                    try writer.writeAll(" . ");
                    try rest.format("", options, writer);
                }
                try writer.writeAll(")");
            },
        }
    }
};

pub const Parser = struct {
    // TODO: keep track of col/row
    remaining_text: []const u8,

    fn skipWhitespace(self: *Parser) void {
        self.remaining_text = std.mem.trimLeft(u8, self.remaining_text, &std.ascii.whitespace);
        while (std.mem.startsWith(u8, self.remaining_text, "//")) {
            if (std.mem.indexOfScalar(u8, self.remaining_text, '\n')) |end| {
                self.remaining_text = self.remaining_text[(end + 1)..];
                self.remaining_text = std.mem.trimLeft(u8, self.remaining_text, &std.ascii.whitespace);
            } else {
                self.remaining_text = self.remaining_text[self.remaining_text.len..];
            }
        }
    }

    fn eatChar(self: *Parser, expected: u8) !void {
        if (!self.eatCharIfPossible(expected)) return error.NotFoundExpectedChar;
    }

    fn eatCharIfPossible(self: *Parser, expected: u8) bool {
        if (self.remaining_text.len > 0 and self.remaining_text[0] == expected) {
            self.remaining_text = self.remaining_text[1..];
            return true;
        } else return false;
    }

    pub fn next(self: *Parser, bank: *Sexpr.Bank) !?*const Sexpr {
        self.skipWhitespace();
        if (self.remaining_text.len == 0) {
            return null;
        } else if (self.eatCharIfPossible('(')) {
            return self.parseSexprInsideParens(bank);
        } else {
            return self.parseAtom(bank);
        }
    }

    fn parseSexprInsideParens(self: *Parser, bank: *Sexpr.Bank) error{ OutOfMemory, UnexpectedEOF, NotFoundExpectedChar }!*const Sexpr {
        self.skipWhitespace();
        if (self.eatCharIfPossible(')'))
            return Sexpr.builtin.nil;
        if (self.eatCharIfPossible('.')) {
            const sentinel = (try self.next(bank)).?;
            try self.eatChar(')');
            return sentinel;
        }
        const first = try self.next(bank) orelse return error.UnexpectedEOF;
        const rest = try self.parseSexprInsideParens(bank);
        return bank.doPair(first, rest);
    }

    fn parseAtom(self: *Parser, bank: *Sexpr.Bank) !*const Sexpr {
        self.skipWhitespace();
        const word_breaks = .{ '(', ')', ':', '.', ';' } ++ std.ascii.whitespace;
        const word_len = std.mem.indexOfAnyPos(u8, self.remaining_text, 0, &word_breaks) orelse self.remaining_text.len;
        const word = self.remaining_text[0..word_len];
        self.remaining_text = self.remaining_text[word_len..];
        return bank.doAtom(word);
    }
};

fn isNumber(buf: []const u8) bool {
    for (buf) |c| if (!std.ascii.isDigit(c)) return false;
    return true;
}

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
