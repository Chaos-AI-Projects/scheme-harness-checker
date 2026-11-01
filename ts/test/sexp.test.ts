import { test } from "node:test";
import assert from "node:assert/strict";
import { Char, Dotted, Vec, car, cdr, equal, isList, isPair, readAll, readOne, sym, write } from "../src/sexp.ts";

test("symbols are interned, so one name is one object", () => {
  assert.equal(sym("foo"), sym("foo"));
  assert.notEqual(sym("foo"), sym("bar"));
});

test("a proper list reads as an array of data", () => {
  assert.deepEqual(readOne("(define (f x) 1 \"s\" #t #f)"), [
    sym("define"),
    [sym("f"), sym("x")],
    1,
    "s",
    true,
    false,
  ]);
});

test("quote marks read as two-element lists", () => {
  assert.deepEqual(readOne("'a"), [sym("quote"), sym("a")]);
  assert.deepEqual(readOne("`(a ,b ,@c)"), [
    sym("quasiquote"),
    [sym("a"), [sym("unquote"), sym("b")], [sym("unquote-splicing"), sym("c")]],
  ]);
});

test("a dotted list reads as Dotted, and cdr walks it", () => {
  const d = readOne("(a b . c)");
  assert.ok(d instanceof Dotted);
  assert.equal(isPair(d), true);
  assert.equal(isList(d), false);
  assert.equal(car(d), sym("a"));
  assert.equal(cdr(cdr(d)), sym("c"));
});

test("cdr of a proper list is a proper list, ending in the empty list", () => {
  const l = readOne("(a b)");
  assert.deepEqual(cdr(l), [sym("b")]);
  assert.deepEqual(cdr(cdr(l)), []);
  assert.equal(isPair(cdr(cdr(l))), false);
  assert.equal(isList(cdr(cdr(l))), true);
});

test("vectors and characters are not pairs", () => {
  const v = readOne("#(1 2)");
  assert.ok(v instanceof Vec);
  assert.equal(isPair(v), false);
  const c = readOne("#\\a");
  assert.ok(c instanceof Char);
  assert.equal(write(readOne("#\\space")), "#\\space");
});

test("comments are skipped and every top-level form is read", () => {
  const forms = readAll("; line\n(a) #| block |# #;(skipped) b [c d]");
  assert.deepEqual(forms, [[sym("a")], sym("b"), [sym("c"), sym("d")]]);
});

test("a symbol may carry an R6RS inline hex escape, as Chez writes -~1", () => {
  assert.deepEqual(readOne("(\\x2D;~1 a)"), [sym("-~1"), sym("a")]);
  assert.equal(readOne("a\\x41;b"), sym("aAb"));
  assert.throws(() => readAll("\\x2D"));
});

test("write prints data the way Scheme's write does", () => {
  assert.equal(write(readOne("(x y #t)")), "(x y #t)");
  assert.equal(write(readOne("(a . b)")), "(a . b)");
  assert.equal(write(readOne("(f \"q\\\"\" -3 #(1))")), "(f \"q\\\"\" -3 #(1))");
  assert.equal(write([]), "()");
});

test("equal compares structure, and fresh reads are distinct objects", () => {
  const a = readOne("(g x)");
  const b = readOne("(g x)");
  assert.notEqual(a, b);
  assert.equal(equal(a, b), true);
  assert.equal(equal(a, readOne("(g y)")), false);
  assert.equal(equal(readOne("(a . b)"), readOne("(a b)")), false);
});

test("unbalanced input throws", () => {
  assert.throws(() => readAll("(a b"));
  assert.throws(() => readAll(")"));
});
