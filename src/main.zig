//! Env = ref to: ( list_of_local_bindings . list_of_parent_envs )

const sample_vau_program =
    \\ ($define! factorial ($lambda (n) ($if (=? n 0) 1 (* n (factorial (- n 1))))))
    \\ (print (factorial 3))
;

test "caaddadr" {
    var bank = Sexpr.Bank.init(std.testing.allocator);
    defer bank.deinit();
    const v = try parseSingle(&bank, "(a . (b . ((c1 . c2) . d)))");
    try std.testing.expect(v.at(.l).equals(atom("a")));
    try std.testing.expect(v.at(.rl).equals(atom("b")));
    try std.testing.expect(v.at(.rrl).equals(bank.doPair(atom("c1"), atom("c2"))));
    try std.testing.expect(v.at(.rrr).equals(atom("d")));
}

test "nth" {
    var bank = Sexpr.Bank.init(std.testing.allocator);
    defer bank.deinit();
    const v = try parseSingle(&bank, "(a b c d)");
    try expectEqual(v.nth(0), atom("a"));
    try expectEqual(v.nth(1), atom("b"));
    try expectEqual(v.nth(2), atom("c"));
    try expectEqual(v.nth(3), atom("d"));
}

test "builtin" {
    try testHelper(std.testing.allocator,
        \\ (builtin . foo)
    , "(builtin . foo)");
}

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

test "$if" {
    try testHelper(std.testing.allocator,
        \\ ($define! x 1)
        \\ ($if true x y)
    , "1");
    try testHelper(std.testing.allocator,
        \\ ($define! x 1)
        \\ ($if false y x)
    , "1");
}

test "=?" {
    try testHelper(std.testing.allocator,
        \\ (=? 1 2)
    , "false");

    try testHelper(std.testing.allocator,
        \\ (=? (cons 1 2) (cons 1 2))
    , "true");
}

test "$car" {
    try testHelper(std.testing.allocator,
        \\ ($define! $car ($vau ((a . b)) _ a))
        \\ ($car (1 . 2))
    , "1");
}

test "wrap" {
    try testHelper(std.testing.allocator,
        \\ ($define! my-car (wrap ($vau ((a . b)) _ a)))
        \\ (my-car (cons 1 2))
    , "1");
}

test "eval" {
    try testHelper(std.testing.allocator,
        \\ (eval ($quote (cons 1 2)) (get-current-env))
    , "(1 . 2)");
}

test "$lambda" {
    try testHelper(std.testing.allocator,
        \\ ($define! foo ($lambda ((a . b)) a))
        \\ (foo (cons 1 2))
    , "1");
}

test "split" {
    try testHelper(std.testing.allocator,
        \\ (split ($quote hola))
    , "(h o l a)");
}

test "fuse" {
    try testHelper(std.testing.allocator,
        \\ (fuse ($quote (h o l a)))
    , "hola");
}

test "$sequence" {
    try testHelper(std.testing.allocator,
        \\ ($sequence
        \\   ($define! x 1)
        \\   ($define! y 2)
        \\   ($define! z (cons x y))
        \\   z)
    , "(1 . 2)");
}

test "$let" {
    try testHelper(std.testing.allocator,
        \\ ($let (x 1) x)
    , "1");
}

test "apply" {
    try testHelper(std.testing.allocator,
        \\ (apply ($lambda (x y) (cons y x)) ($quote (1 2)) (make-env))
    , "(2 . 1)");
}

test "weird apply" {
    try testHelper(std.testing.allocator,
        \\ (apply ($lambda x x) 2 (make-env))
    , "2");
}

test "$cond" {
    try testHelper(std.testing.allocator,
        \\ ($cond
        \\   (false 1)
        \\   ((=? 1 1) 2)
        \\ )
    , "2");
}

test "reverse" {
    try testHelper(std.testing.allocator,
        \\ (reverse ($quote (a b c)))
    , "(c b a)");
}

// test "binaryFromChar" {
//     try testHelper(std.testing.allocator,
//         \\ (binaryFromChar 6)
//     , "(b0 b1 b1)");
// }

// test "car" {
//     try testHelper(std.testing.allocator,
//         \\ ($define! $car ($vau (a . b) _ a))
//         \\ ($define! car ($vau (x) env (eval (cons $car (eval x env)) env))
//         \\ (car (cons 1 2))
//     , "1");
// }

// test "list" {
//     try testHelper(std.testing.allocator,
//         \\ ($define! list ($vau args env
//         \\     ($match args
//         \\         (#nil        nil)
//         // \\      ((@h . @t)   (cons (eval h env) (combine list t env)))
//         \\         ((@h . @t)   (cons (eval h env) (eval (cons list t) env)))
//         \\ )))
//         \\ ($define! x 1)
//         \\ (list x x)
//     , "(1 1)");
// }

// test "list" {
//     try testHelper(std.testing.allocator,
//         \\ ($define! list ($vau args env
//         \\     ($if (=? args nil)
//         \\         nil
//         \\         (cons (car args) (list (cdr args))))))
//         \\ ($define! x 1)
//         \\ (list x x)
//     , "(1 1)");
// }

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
        last_value = rawEval(v, env, &bank);
    }
    try expectEqual(expected, last_value);
}

pub fn expectEqual(expected: Sexpr, actual: Sexpr) !void {
    errdefer std.log.err("Expected\n\t{any}\nFound\n\t{any}\n", .{ expected, actual });
    try std.testing.expect(actual.equals(expected));
}

fn atom(v: []const u8) Sexpr {
    return .{ .atom = .{ .value = v } };
}

fn parseSingle(bank: *Sexpr.Bank, source: []const u8) !Sexpr {
    var parser: Parser = .{ .remaining_text = source };
    const result = (try parser.next(bank)).?;
    assert(try parser.next(bank) == null);
    return result;
}

const Builtin = struct {
    pub fn @"$define!"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const formal_tree = arguments.nth(0);
        const value = rawEval(arguments.nth(1), env, bank);
        bind(formal_tree, value, env, bank);
        return Sexpr.builtin.@"#inert";
    }

    pub fn @"$vau"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        return bank.doPair(atom("compiled_vau"), bank.doPair(env, arguments));
    }

    pub fn cons(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const left = rawEval(arguments.nth(0), env, bank);
        const right = rawEval(arguments.nth(1), env, bank);
        return bank.doPair(left, right);
    }

    pub fn @"$if"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const condition = rawEval(arguments.nth(0), env, bank);
        std.log.debug("condition: {any}", .{condition});
        std.log.debug("arguments: {any}", .{arguments});
        if (condition.equals(Sexpr.builtin.true)) {
            std.log.debug("evaluating true: {any}", .{arguments.nth(1)});
            return rawEval(arguments.nth(1), env, bank);
        } else {
            assertEqual(condition, Sexpr.builtin.false);
            std.log.debug("evaluating false: {any}", .{arguments.nth(2)});
            return rawEval(arguments.nth(2), env, bank);
        }
    }

    pub fn @"=?"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const left = rawEval(arguments.nth(0), env, bank);
        const right = rawEval(arguments.nth(1), env, bank);
        return if (left.equals(right)) Sexpr.builtin.true else Sexpr.builtin.false;
    }

    pub fn @"$quote"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        _ = env;
        _ = bank;
        return arguments.nth(0);
    }

    pub fn wrap(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const vau = rawEval(arguments.nth(0), env, bank);
        assertEqual(vau.at(.l), atom("compiled_vau"));
        return bank.doPair(atom("wrapped_vau"), vau);
    }

    pub fn unwrap(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const wrapped_vau = rawEval(arguments.nth(0), env, bank);
        assertEqual(wrapped_vau.at(.l), atom("wrapped_vau"));
        return wrapped_vau.at(.r);
    }

    pub fn eval(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        return rawEval(
            rawEval(arguments.nth(0), env, bank),
            rawEval(arguments.nth(1), env, bank),
            bank,
        );
    }

    pub fn split(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        const arg = rawEval(arguments.nth(0), env, bank);
        assertAtom(arg);
        const value = arg.atom.value;
        var result = Sexpr.builtin.nil;
        for (0..value.len) |k| {
            const i = value.len - k;
            result = bank.doPair(atom(value[i - 1 .. i]), result);
        }
        return result;
    }

    pub fn fuse(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        var arg = rawEval(arguments.nth(0), env, bank);
        assertList(arg);
        bank.stringBegin();
        while (arg.is(.pair)) {
            const head = arg.pair.left.*;
            assertAtom(head);
            bank.stringAdd(head.atom.value);
            arg = arg.pair.right.*;
        }
        const value = bank.stringEnd();
        return atom(value);
    }

    pub fn @"$sequence"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        var last_value = Sexpr.builtin.@"#inert";
        var remaining_args = arguments;
        while (remaining_args.is(.pair)) {
            const head = remaining_args.at(.l);
            remaining_args = remaining_args.at(.r);
            last_value = rawEval(head, env, bank);
        }
        return last_value;
    }

    pub fn @"make-env"(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
        var parent_envs_buffer: std.ArrayList(Sexpr) = .init(std.heap.smp_allocator);
        defer parent_envs_buffer.deinit();

        var remaining_args = arguments;
        while (remaining_args.is(.pair)) {
            const head = remaining_args.at(.l);
            remaining_args = remaining_args.at(.r);
            parent_envs_buffer.append(rawEval(head, env, bank)) catch @panic("OoM");
        }
        const parent_envs_sexpr = bank.doList(parent_envs_buffer.items);
        return bank.doRef(bank.doPair(Sexpr.builtin.nil, parent_envs_sexpr));
    }

    comptime {
        const ExpectedSignature = fn (arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr;
        const expected_info = @typeInfo(ExpectedSignature).@"fn";
        for (@typeInfo(@This()).@"struct".decls) |decl| {
            const ActualSignature = @TypeOf(@field(@This(), decl.name));
            const actual_info = @typeInfo(ActualSignature).@"fn";

            if (!(actual_info.is_generic == expected_info.is_generic and
                actual_info.is_var_args == expected_info.is_var_args and
                actual_info.return_type == expected_info.return_type and
                std.mem.eql(std.builtin.Type.Fn.Param, actual_info.params, expected_info.params)))
            {
                @compileError(std.fmt.comptimePrint("Bad signature for builtin method {s}", .{decl.name}));
            }
        }
    }
};

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

    const stdin = std.io.getStdIn().reader();

    var bank = Sexpr.Bank.init(gpa);
    defer bank.deinit();
    var strings_bank: std.heap.ArenaAllocator = .init(gpa);
    defer strings_bank.deinit();
    const env = makeKernelStandardEnvironment(&bank);

    // TODO: this should be (loop (print (eval (read) env))), rather than a special case
    try stdout.print("> ", .{});
    try bw.flush();
    while (try stdin.readUntilDelimiterOrEofAlloc(strings_bank.allocator(), '\n', std.math.maxInt(usize))) |line| {
        var parser: Parser = .{ .remaining_text = line };
        while (try parser.next(&bank)) |v| {
            try stdout.print("read: {any}\n", .{v});
            try stdout.print("eval'd: {any}\n", .{rawEval(v, env, &bank)});
        }
        try stdout.print("> ", .{});
        try bw.flush();
    }
}

fn makeKernelStandardEnvironment(bank: *Sexpr.Bank) Sexpr {
    // TODO: do this at comptime, or at least cache it
    var ground_environment_definitions = Sexpr.builtin.nil;
    inline for (@typeInfo(Builtin).@"struct".decls) |decl| {
        const name = decl.name;
        ground_environment_definitions = bank.doPair(
            bank.doPair(
                atom(name),
                bank.doPair(
                    atom("builtin"),
                    atom(name),
                ),
            ),
            ground_environment_definitions,
        );
    }
    const ground_environment: Sexpr = .{ .ref = bank.store(bank.doPair(ground_environment_definitions, Sexpr.builtin.nil)) };

    var parser: Parser = .{ .remaining_text = 
        \\ ($define! get-current-env (wrap ($vau () e e)))
        \\ ($define! list (wrap ($vau x _ x)))
        \\ ($define! $lambda
        \\   ($vau (params body) env
        \\     (wrap (eval (list $vau params _ body) env))))
        \\ ($define! empty? ($lambda (l) (=? l ())))
        \\ ($define! apply ($lambda (applicative arguments env)
        \\   (eval (cons (unwrap applicative) arguments) env)))
        \\ ($define! $let ($vau ((pattern value) body) env
        \\   (eval (list (list ($quote $lambda) (list pattern) body) value) env)))
        \\ ($define! $cond
        \\   ($vau clauses env
        \\     ($if (empty? clauses)
        \\       error_NoMatchingCondCase
        \\       ($let (((test body) . clauses) clauses)
        \\         ($if (eval test env)
        \\           (eval body env)
        \\           (apply (wrap $cond) clauses env))))))
        \\ ($define! car ($lambda ((a . b)) a))
        \\ ($define! cdr ($lambda ((a . b)) b))
        \\ // ($define! concat ($lambda lists ($if (empty? lists) () (concat (car lists) (append)))))
        \\ ($define! append-element ($lambda (value lst) ($if (empty? lst) (list value) (cons (car lst) (append-element value (cdr lst))))))
        \\ ($define! reverse ($lambda (lst) ($if (empty? lst) () (append-element (car lst) (reverse (cdr lst))))))
        \\ 
        \\ // TODO: use a cool macro here
        \\ ($define! binary-from-char ($lambda (char) ($cond
        \\   ((=? char 0) ($quote ()))
        \\   ((=? char 1) ($quote (b1)))
        \\   ((=? char 2) ($quote (b0 b1)))
        \\   ((=? char 3) ($quote (b1 b1)))
        \\   ((=? char 4) ($quote (b0 b0 b1)))
        \\   ((=? char 5) ($quote (b1 b0 b1)))
        \\   ((=? char 6) ($quote (b0 b1 b1)))
        \\   ((=? char 7) ($quote (b1 b1 b1)))
        \\   ((=? char 8) ($quote (b0 b0 b0 b1)))
        \\   ((=? char 9) ($quote (b1 b0 b0 b1)))
        \\ )))
        \\ ($define! binary-from-text ($lambda (text)
        \\   (binary-from-base-10 (reverse (split text)))))
        \\ ($define! binary-from-base-10 ($lambda (digits)
        \\   ($if (empty? digits) 
        \\     ()
        \\     (TODO))))
        \\ 
    };
    while (parser.next(bank) catch @panic("bad text")) |v| {
        _ = rawEval(v, ground_environment, bank);
    }

    return bank.doRef(bank.doPair(Sexpr.builtin.nil, bank.doPair(ground_environment, Sexpr.builtin.nil)));
}

fn nth(l: Sexpr, index: usize) Sexpr {
    return l.nth(index);
}

fn lookup(key: Sexpr, env: Sexpr) ?Sexpr {
    assertAtom(key);
    assertEnv(env);

    // self evaluating symbols
    if (isNumber(key.atom.value)) return key;
    for ([_][]const u8{ "true", "false", "nil", "_" }) |word| {
        if (key.equals(.{ .atom = .{ .value = word } })) return key;
    }

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
    const local_bindings = env.at(._l);
    const parent_envs = env.at(._r);
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
        bind(definiend.at(.l), expression.at(.l), env, bank);
        bind(definiend.at(.r), expression.at(.r), env, bank);
    }
}

fn rawEval(expr: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
    assertEnv(env);
    switch (expr) {
        .ref => panic("Don't know how to eval a ref", .{}),
        .atom => return lookup(expr, env) orelse panic("unbound variable: {any}", .{expr}),
        .pair => |pair| {
            inline for (.{ "builtin", "compiled_vau", "wrapped_vau" }) |v| {
                if (pair.left.*.equals(atom(v))) return expr;
            }
            const operative = rawEval(pair.left.*, env, bank);
            const arguments = pair.right.*;
            if (operative.is(.pair) and operative.at(.l).equals(atom("builtin")) and operative.at(.r).is(.atom)) {
                const name = operative.at(.r).atom.value;
                inline for (@typeInfo(Builtin).@"struct".decls) |decl| {
                    if (std.mem.eql(u8, decl.name, name)) {
                        const builtin_fn = @field(Builtin, decl.name);
                        return builtin_fn(arguments, env, bank);
                    }
                }
            }
            if (operative.is(.pair) and operative.at(.l).equals(.{ .atom = .{ .value = "compiled_vau" } })) {
                const static_env = operative.at(.rl);
                const formal_tree = operative.at(.rrl);
                const dynamic_env_name = operative.at(.rrrl);
                const body_expr = operative.at(.rrrrl);

                var temp_env = bank.doPair(Sexpr.builtin.nil, bank.doPair(static_env, Sexpr.builtin.nil));
                bind(formal_tree, arguments, .{ .ref = &temp_env }, bank);
                bind(dynamic_env_name, env, .{ .ref = &temp_env }, bank);
                return rawEval(body_expr, .{ .ref = &temp_env }, bank);
            } else if (operative.is(.pair) and operative.at(.l).equals(.{ .atom = .{ .value = "wrapped_vau" } })) {
                const vau = operative.at(.r);
                const evaluated_arguments = evaluateEachArgument(arguments, env, bank);
                return rawEval(bank.doPair(bank.doPair(atom("$quote"), bank.doPair(vau, Sexpr.builtin.nil)), evaluated_arguments), env, bank);
            } else {
                panic("Bad operative: \"{any}\"", .{operative});
            }
        },
    }
}

fn evaluateEachArgument(arguments: Sexpr, env: Sexpr, bank: *Sexpr.Bank) Sexpr {
    assertList(arguments);
    if (arguments.equals(Sexpr.builtin.nil)) {
        return Sexpr.builtin.nil;
    } else {
        return bank.doPair(
            rawEval(arguments.at(.l), env, bank),
            evaluateEachArgument(arguments.at(.r), env, bank),
        );
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
        strings_arena: std.heap.ArenaAllocator,
        string_builder: std.ArrayList(u8),

        pub fn init(allocator: std.mem.Allocator) Bank {
            return .{
                .pool = .init(allocator),
                .strings_arena = .init(allocator),
                .string_builder = .init(allocator),
            };
        }

        pub fn deinit(self: *Bank) void {
            self.pool.deinit();
            self.strings_arena.deinit();
            assert(self.string_builder.items.len == 0);
            self.string_builder.deinit();
        }

        pub fn stringBegin(self: *Bank) void {
            assert(self.string_builder.items.len == 0);
        }

        pub fn stringAdd(self: *Bank, v: []const u8) void {
            self.string_builder.appendSlice(v) catch @panic("OoM");
        }

        pub fn stringEnd(self: *Bank) []const u8 {
            const value = self.strings_arena.allocator().dupe(u8, self.string_builder.items) catch @panic("OoM");
            self.string_builder.clearRetainingCapacity();
            return value;
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

        pub fn doList(self: *Bank, values: []const Sexpr) Sexpr {
            if (values.len == 0) return Sexpr.builtin.nil;
            return self.doPair(values[0], self.doList(values[1..]));
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
            .ref => |this_ref| this_ref == other.ref,
        };
    }

    pub fn is(this: *const Sexpr, kind: std.meta.FieldEnum(Sexpr)) bool {
        return std.meta.activeTag(this.*) == kind;
    }

    pub fn at(v: Sexpr, comptime address: @Type(.enum_literal)) Sexpr {
        var res = v;
        inline for (@tagName(address)) |item| {
            res = switch (item) {
                'l' => res.pair.left.*,
                'r' => res.pair.right.*,
                '_' => res.ref.*,
                else => @compileError(std.fmt.comptimePrint("bad address item: {s}", .{item})),
            };
        }
        return res;
    }

    pub fn nth(l: Sexpr, index: usize) Sexpr {
        assertPair(l);
        var cur = l;
        for (0..index) |_| {
            cur = cur.pair.right.*;
            assertPair(cur);
        }
        return cur.pair.left.*;
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
            .ref => try writer.print("<ref>", .{}), // TODO: print some value
            // .ref => |ref| try writer.print("<{any}>", .{ref.*}), // TODO: avoid printing cyclic values
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
