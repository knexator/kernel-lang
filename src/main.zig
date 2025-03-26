//! Env = ref to: ( list_of_local_bindings . list_of_parent_envs )

const sample_vau_program =
    \\ ($define! factorial ($lambda (n) ($if (=? n 0) 1 (* n (factorial (- n 1))))))
    \\ (print (factorial 3))
;

test "cons" {
    try testHelper(std.testing.allocator,
        \\ ($define! a 10)
        \\ (cons a a)
    , "(10 . 10)");
}

test "$define!" {
    try testHelper(std.testing.allocator,
        // \\ ($define! ((a) . b) (cons (list 10) 11))
        \\ ($define! a 10)
        \\ a
    , "10");
}

test "$vau" {
    try testHelper(std.testing.allocator,
        \\ ($define! foo ($vau (x y) _ x))
        \\ (foo a b)
    , "a");
}

test "static parent env" {
    try testHelper(std.testing.allocator,
        \\ ($define! x 1)
        \\ ($define! foo ($vau () _ x))
        \\ (foo)
    , "1");
}

test "modify static parent env" {
    try testHelper(std.testing.allocator,
        \\ ($define! x 1)
        \\ ($define! foo ($vau () _ x))
        \\ ($define! x 2)
        \\ (foo)
    , "2");
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
    const env = makeKernelStandardEnvironment(&bank);
    var last_value = Sexpr.builtin.@"#inert";
    while (parser.next(&bank) catch @panic("bad text")) |v| {
        last_value = eval(v, env, &bank);
    }
    try std.testing.expect(last_value.equals(expected));
}

const ground_environment: Sexpr = .{ .ref = @constCast(&Sexpr{ .pair = .{
    .left = &.{ .pair = .{
        .left = &.{ .pair = .{
            .left = &.{ .atom = .{ .value = "$define!" } },
            .right = &.{ .pair = .{
                .left = &.{ .atom = .{ .value = "builtin" } },
                .right = &.{ .atom = .{ .value = "$define!" } },
            } },
        } },
        .right = &.{ .pair = .{
            .left = &.{ .pair = .{
                .left = &.{ .atom = .{ .value = "$vau" } },
                .right = &.{ .pair = .{
                    .left = &.{ .atom = .{ .value = "builtin" } },
                    .right = &.{ .atom = .{ .value = "$vau" } },
                } },
            } },
            .right = &.{ .pair = .{
                .left = &.{ .pair = .{
                    .left = &.{ .atom = .{ .value = "cons" } },
                    .right = &.{ .pair = .{
                        .left = &.{ .atom = .{ .value = "builtin" } },
                        .right = &.{ .atom = .{ .value = "cons" } },
                    } },
                } },
                .right = &Sexpr.builtin.nil,
            } },
        } },
    } },
    .right = &Sexpr.builtin.nil,
} }) };

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
        \\ ($define! (a . b) (cons 10 11))
        \\ a
        \\ b
    };

    const env = makeKernelStandardEnvironment(&bank);

    while (try parser.next(&bank)) |v| {
        try stdout.print("read: {any}\n", .{v});
        try stdout.print("eval'd: {any}\n", .{eval(v, env, &bank)});
    }
}

fn makeKernelStandardEnvironment(bank: *Sexpr.Bank) Sexpr {
    return bank.doRef(bank.doPair(Sexpr.builtin.nil, bank.doPair(ground_environment, Sexpr.builtin.nil)));
}

fn nth(l: Sexpr, index: usize) Sexpr {
    assertPair(l);
    var cur = l;
    for (0..index) |_| {
        cur = l.pair.right.*;
        assertPair(cur);
    }
    return cur.pair.left.*;
}

fn lookup(key: Sexpr, env: Sexpr) ?Sexpr {
    assertAtom(key);
    assertEnv(env);

    // self evaluating symbols
    if (isNumber(key.atom.value)) return key;

    const local_bindings = env.ref.*.pair.left.*;
    const parent_envs = env.ref.*.pair.right.*;

    var remaining_bindings = local_bindings;
    while (remaining_bindings.is(.pair)) {
        const entry = remaining_bindings.pair.left.*;
        remaining_bindings = remaining_bindings.pair.right.*;
        assertPair(entry);
        assertAtom(entry.pair.left.*);
        if (entry.pair.left.atom.equals(key.atom)) {
            return entry.pair.right.*;
        }
    }
    assertEqual(remaining_bindings, Sexpr.builtin.nil);

    var remaining_parent_envs = parent_envs;
    while (remaining_parent_envs.is(.pair)) {
        const parent_env = remaining_parent_envs.pair.left.*;
        remaining_parent_envs = remaining_parent_envs.pair.right.*;
        if (lookup(key, parent_env)) |result| {
            return result;
        }
    }
    assertEqual(remaining_parent_envs, Sexpr.builtin.nil);

    return null;
}

fn addToEnv(key: Sexpr, value: Sexpr, env: Sexpr, bank: *Sexpr.Bank) void {
    const local_bindings = env.ref.*.pair.left.*;
    const parent_envs = env.ref.*.pair.right.*;
    env.ref.* = bank.doPair(
        bank.doPair(bank.doPair(key, value), local_bindings),
        parent_envs,
    );
}

fn bind(definiend: Sexpr, expression: Sexpr, env: Sexpr, bank: *Sexpr.Bank) void {
    assertEnv(env);
    if (definiend.equals(Sexpr.builtin.nil)) {
        assertNil(expression);
    } else if (definiend.equals(Sexpr.builtin._)) {
        // nothing
    } else if (definiend.is(.atom)) {
        addToEnv(definiend, expression, env, bank);
    } else {
        assertPair(expression);
        bind(definiend.pair.left.*, expression.pair.left.*, env, bank);
        bind(definiend.pair.right.*, expression.pair.right.*, env, bank);
    }
}

fn eval(expr: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
    assertEnv(env);
    switch (expr) {
        .ref => panic("Don't know how to eval a ref", .{}),
        .atom => return lookup(expr, env) orelse panic("unbound variable: {any}", .{expr}),
        .pair => |pair| {
            const operative = eval(pair.left.*, env, bank);
            const argument = pair.right.*;
            if (operative.equals(.{ .pair = .{ .left = &.{ .atom = .{ .value = "builtin" } }, .right = &.{ .atom = .{ .value = "$define!" } } } })) {
                const formal_tree = argument.pair.left.*;
                const value = eval(argument.pair.right.pair.left.*, env, bank);
                bind(formal_tree, value, env, bank);
                return Sexpr.builtin.@"#inert";
            } else if (operative.equals(.{ .pair = .{ .left = &.{ .atom = .{ .value = "builtin" } }, .right = &.{ .atom = .{ .value = "$vau" } } } })) {
                return bank.doPair(.{ .atom = .{ .value = "compiled_vau" } }, bank.doPair(env, pair.right.*));
            } else if (operative.equals(.{ .pair = .{ .left = &.{ .atom = .{ .value = "builtin" } }, .right = &.{ .atom = .{ .value = "cons" } } } })) {
                const left = eval(nth(argument, 0), env, bank);
                const right = eval(nth(argument, 1), env, bank);
                return bank.doPair(left, right);
            } else if (operative.is(.pair) and operative.pair.left.equals(.{ .atom = .{ .value = "compiled_vau" } })) {
                const static_env = operative.pair.right.pair.left.*;
                const formal_tree = operative.pair.right.pair.right.pair.left.*;
                const dynamic_env_name = operative.pair.right.pair.right.pair.right.pair.left.*;
                const body_expr = operative.pair.right.pair.right.pair.right.pair.right.pair.left.*;

                var temp_env = bank.doPair(Sexpr.builtin.nil, bank.doPair(static_env, Sexpr.builtin.nil));
                bind(formal_tree, argument, .{ .ref = &temp_env }, bank);
                bind(dynamic_env_name, env, .{ .ref = &temp_env }, bank);
                return eval(body_expr, .{ .ref = &temp_env }, bank);
            } else {
                panic("Bad operative: \"{any}\"", .{operative});
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
        return this.left.equals(other.left.*) and this.right.equals(other.right.*);
    }
};
pub const Sexpr = union(enum) {
    atom: Atom,
    pair: Pair,
    ref: *Sexpr,

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

        pub fn store(self: *Bank, s: Sexpr) *Sexpr {
            const res = self.pool.create() catch @panic("OoM");
            res.* = s;
            return res;
        }

        pub fn doPair(self: *Bank, left: Sexpr, right: Sexpr) Sexpr {
            return .{ .pair = .{
                .left = self.store(left),
                .right = self.store(right),
            } };
        }

        pub fn doRef(self: *Bank, v: Sexpr) Sexpr {
            return .{ .ref = self.store(v) };
        }
    };

    pub const builtin: struct {
        nil: Sexpr = .{ .atom = .{ .value = "nil" } },
        _: Sexpr = .{ .atom = .{ .value = "_" } },
        @"#inert": Sexpr = .{ .atom = .{ .value = "#inert" } },
        true: Sexpr = .{ .atom = .{ .value = "true" } },
        false: Sexpr = .{ .atom = .{ .value = "false" } },
    } = .{};

    pub fn equals(this: Sexpr, other: Sexpr) bool {
        if (std.meta.activeTag(this) != std.meta.activeTag(other)) return false;
        return switch (this) {
            .atom => |this_atom| this_atom.equals(other.atom),
            .pair => |this_pair| this_pair.equals(other.pair),
            .ref => @panic("TODO"),
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
            .ref => |ref| try writer.print("<{any}>", .{ref.*}), // TODO: avoid printing cyclic values
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

    pub fn next(self: *Parser, bank: *Sexpr.Bank) !?Sexpr {
        self.skipWhitespace();
        if (self.remaining_text.len == 0) {
            return null;
        } else if (self.eatCharIfPossible('(')) {
            return try self.parseSexprInsideParens(bank);
        } else {
            return try self.parseAtom();
        }
    }

    fn parseSexprInsideParens(self: *Parser, bank: *Sexpr.Bank) error{ OutOfMemory, UnexpectedEOF, NotFoundExpectedChar }!Sexpr {
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

    fn parseAtom(self: *Parser) !Sexpr {
        self.skipWhitespace();
        const word_breaks = .{ '(', ')', ':', '.', ';' } ++ std.ascii.whitespace;
        const word_len = std.mem.indexOfAnyPos(u8, self.remaining_text, 0, &word_breaks) orelse self.remaining_text.len;
        const word = self.remaining_text[0..word_len];
        self.remaining_text = self.remaining_text[word_len..];
        return .{ .atom = .{ .value = word } };
    }
};

fn assertPair(v: Sexpr) void {
    if (!v.is(.pair)) panic("Expected a Pair, found \"{any}\"", .{v});
}

fn assertAtom(v: Sexpr) void {
    if (!v.is(.atom)) panic("Expected an Atom, found \"{any}\"", .{v});
}

fn assertRef(v: Sexpr) void {
    if (!v.is(.ref)) panic("Expected a Ref, found \"{any}\"", .{v});
}

fn assertNil(v: Sexpr) void {
    assertEqual(v, Sexpr.builtin.nil);
}

fn assertEnv(env: Sexpr) void {
    assertRef(env);
    assertPair(env.ref.*);
    assertList(env.ref.*.pair.left.*);
    assertList(env.ref.*.pair.right.*);
}

fn assertList(v: Sexpr) void {
    if (v.is(.atom)) {
        assertNil(v);
    } else {
        assertPair(v);
        assertList(v.pair.right.*);
    }
}

fn assertEqual(a: Sexpr, b: Sexpr) void {
    if (!a.equals(b)) panic("Expected equality between\n\t{any}\nand\n\t{any}", .{ a, b });
}

fn isNumber(buf: []const u8) bool {
    for (buf) |c| if (!std.ascii.isDigit(c)) return false;
    return true;
}

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const panic = std.debug.panic;
