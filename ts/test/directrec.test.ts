// The direct-recursion pass of termination.ss (HC-17, Phase 5). Cases are the "Direct recursion
// analysis" groups of test-termination.ss (from line 736). Each program there has no named let, do
// loop or mutual recursion that fails, so this pass alone decides its verdict.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, readOne, sym, write } from "../src/sexp.ts";
import { analyzeDirectRecursion, extractFormals, findDefinitionForm, findFormalsFor } from "../src/termination/directrec.ts";

const check = (source: string) => analyzeDirectRecursion(readAll(source));

const accepted: [name: string, source: string][] = [
  ["factorial", "(define (fact n) (if (<= n 0) 1 (* n (fact (- n 1)))))"],
  ["list length", "(define (f xs) (if (null? xs) 0 (+ 1 (f (cdr xs)))))"],
  ["fibonacci", "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))"],
  ["multi-arg with one decreasing", "(define (f x y) (if (null? x) y (f (cdr x) (+ y 1))))"],
  ["non-recursive function", "(define (add x y) (+ x y))"],
  ["define-lambda factorial", "(define fact (lambda (n) (if (<= n 0) 1 (* n (fact (- n 1))))))"],
  ["letrec with decrease + base", "(letrec ((f (lambda (n) (if (<= n 0) 0 (f (- n 1)))))) (f 10))"],
  ["sub1 decrease", "(define (count n) (if (<= n 0) 0 (count (sub1 n))))"],
  ["cond base case", "(define (f n) (cond ((<= n 0) 0) (else (f (- n 1)))))"],
  ["higher-order not flagged", "(define (apply-f f x) (f x))"],
  [
    "mutual recursion left to Phase 6",
    "(define (even? n) (if (<= n 0) #t (odd? (- n 1)))) (define (odd? n) (if (<= n 0) #f (even? (- n 1))))",
  ],
];

for (const [name, source] of accepted) {
  test(`direct recursion accepts: ${name}`, () => assert.deepEqual(check(source), []));
}

const rejected: [name: string, source: string, kind: string][] = [
  ["no decrease no base", "(define (f n) (f n))", "no-decreasing-arg"],
  ["increasing arg", "(define (f n) (if (zero? n) 0 (f (+ n 1))))", "no-decreasing-arg"],
  ["decrease but no base", "(define (f n) (f (- n 1)))", "no-base-case"],
  ["base but no decrease", "(define (f n) (if (zero? n) 0 (f n)))", "no-decreasing-arg"],
  ["letrec no decrease", "(letrec ((f (lambda (n) (f n)))) (f 10))", "no-decreasing-arg"],
  ["rest argument fails closed", "(define (f . xs) (if (null? xs) 0 (apply f (cdr xs))) (f))", "no-decreasing-arg"],
  ["no formals", "(define (f) (f))", "no-decreasing-arg"],
];

for (const [name, source, kind] of rejected) {
  test(`direct recursion rejects: ${name}`, () => {
    const violations = check(source);
    assert.equal(violations.length, 1);
    assert.equal(violations[0]!.kind, kind);
    assert.equal(violations[0]!.function, sym("f"));
  });
}

test("the violation carries the defining form by identity", () => {
  const exprs = readAll("(define (g x) 1) (define (f n) (f n))");
  assert.equal(analyzeDirectRecursion(exprs)[0]!.expr, exprs[1]);
});

test("a letrec binding's violation carries the letrec", () => {
  const exprs = readAll("(letrec ((f (lambda (n) (f n)))) (f 10))");
  assert.equal(analyzeDirectRecursion(exprs)[0]!.expr, exprs[0]);
});

test("reasons match the Scheme's text", () => {
  assert.equal(check("(define (f n) (f n))")[0]!.reason, 'recursive function "f" has no decreasing argument in recursive call(s)');
  assert.equal(check("(define (f n) (f (- n 1)))")[0]!.reason, 'recursive function "f" has no reachable base case');
  assert.equal(
    check("(define (f n) (if (= n 0) 0 (f (- n 2))))")[0]!.reason,
    'recursive function "f" has no decreasing argument in recursive call(s); (= n 0) does not bound n from below, use (<= n 0)',
  );
});

test("extractFormals: the three definition shapes", () => {
  assert.equal(write(extractFormals(readOne("(define (f a b) a)"))!), "(a b)");
  assert.equal(write(extractFormals(readOne("(define f (lambda (a) a))"))!), "(a)");
  assert.equal(write(extractFormals(readOne("(f (lambda (a b) a))"))!), "(a b)");
  assert.equal(extractFormals(readOne("(define (f a . r) a)")), null);
  assert.equal(extractFormals(readOne("(define f (lambda r r))")), null);
  assert.equal(extractFormals(readOne("(define f 1)")), null);
  assert.equal(extractFormals(1), null);
});

test("findFormalsFor and findDefinitionForm find nested and letrec definitions", () => {
  const exprs = readAll("(define (outer x) (define (inner y) y) (letrec ((lp (lambda (i j) i))) (lp x 1)))");
  assert.equal(write(findFormalsFor(exprs, sym("inner"))!), "(y)");
  assert.equal(write(findFormalsFor(exprs, sym("lp"))!), "(i j)");
  assert.equal(findFormalsFor(exprs, sym("missing")), null);
  assert.equal(write(findDefinitionForm(exprs, sym("inner"))!), "(define (inner y) y)");
  assert.equal(car0(findDefinitionForm(exprs, sym("lp"))), "letrec");
});

test("find-definition-form matches a bare (define name) that find-formals-for skips", () => {
  const exprs = readAll("(define f) (define (f n) (f n))");
  assert.equal(findDefinitionForm(exprs, sym("f")), exprs[0]);
  assert.equal(write(findFormalsFor(exprs, sym("f"))!), "(n)");
});

test("find-formals-for searches on past a definition whose formals cannot be extracted", () => {
  // The Scheme's result stays #f there, and its search runs while the result is #f.
  const exprs = readAll("(define (f . x) 3) (define (f n) (f n))");
  assert.equal(write(findFormalsFor(exprs, sym("f"))!), "(n)");
  assert.equal(findDefinitionForm(exprs, sym("f")), exprs[0]);
});

function car0(d: unknown): string {
  return Array.isArray(d) && d[0] && typeof d[0] === "object" && "name" in d[0] ? (d[0] as { name: string }).name : "";
}
