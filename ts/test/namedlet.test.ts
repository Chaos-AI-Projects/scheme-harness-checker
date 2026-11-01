// The named-let pass of termination.ss (HC-16, Phase 4). Cases are the named-let groups of
// test-termination.ss: "Named-let analysis" (from line 512), the three "Conservative" groups (652),
// "Vector index iteration" (1690), and the named-let cases of HC-2 round 3 (1979), HC-7 (2440) and
// HC-6 (2510). Each program there has no recursive define, so this pass alone decides its verdict.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, readOne } from "../src/sexp.ts";
import {
  analyzeNamedLetForms,
  baseCaseTest,
  condFallThroughTest,
  hasBaseCase,
  negatedBaseCaseTest,
} from "../src/termination/namedlet.ts";

const check = (source: string) => analyzeNamedLetForms(readAll(source));

const accepted: [name: string, source: string][] = [
  ["decreasing arg and base case", "(let loop ((n 10)) (if (<= n 0) 0 (loop (- n 1))))"],
  ["sub1 decrease", "(let loop ((n 10)) (if (<= n 0) 0 (loop (sub1 n))))"],
  ["fx- decrease", "(let loop ((n 10)) (if (<= n 0) 0 (loop (fx- n 1))))"],
  ["cdr structural decrease", "(let loop ((lst '(1 2 3))) (if (null? lst) 0 (loop (cdr lst))))"],
  ["cddr structural decrease", "(let loop ((lst '(1 2 3 4))) (if (null? lst) 0 (loop (cddr lst))))"],
  ["list-tail structural decrease", "(let loop ((lst '(1 2 3))) (if (null? lst) 0 (loop (list-tail lst 1))))"],
  ["(not (pair? x)) base case", "(let loop ((lst '(1 2 3))) (if (not (pair? lst)) 0 (loop (cdr lst))))"],
  ["(< x 1) base case", "(let loop ((n 10)) (if (< n 1) 0 (loop (- n 1))))"],
  ["when guard (implicit base case)", "(let loop ((n 10)) (when (> n 0) (display n) (loop (- n 1))))"],
  ["unless guard", "(let loop ((n 10)) (unless (<= n 0) (display n) (loop (- n 1))))"],
  ["cond guard", "(let loop ((n 10)) (cond ((<= n 0) 'done) (else (loop (- n 1)))))"],
  ["multiple args, one decreasing", "(let loop ((n 10) (acc 0)) (if (<= n 0) acc (loop (- n 1) (+ acc n))))"],
  ["nested inside define", "(define (sum-to n) (let loop ((i n) (acc 0)) (if (<= i 0) acc (loop (- i 1) (+ acc i)))))"],
  ["nested valid named-lets", "(let outer ((i 10)) (if (<= i 0) 0 (let inner ((j 5)) (if (<= j 0) (outer (- i 1)) (inner (- j 1))))))"],
  ["non-recursive named-let", "(let loop ((x 1) (y 2)) (+ x y))"],
  ["all calls decrease", "(let loop ((x 10)) (if (<= x 0) 'done (if (even? x) (loop (- x 1)) (loop (- x 2)))))"],
  ["index up with when (< i (vector-length v))", "(let loop ((i 0)) (when (< i (vector-length v)) (process (vector-ref v i)) (loop (+ i 1))))"],
  ["index up with if (>= i (vector-length v))", "(let loop ((i 0)) (if (>= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"],
  ["index up with (= i (vector-length v))", "(let loop ((i 0)) (if (= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"],
  ["index down from vector-length with when (>= i 0)", "(let loop ((i (- (vector-length v) 1))) (when (>= i 0) (process (vector-ref v i)) (loop (- i 1))))"],
  ["add1 step", "(let loop ((i 0)) (if (= i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (add1 i)))))"],
  ["fx+ step", "(let loop ((i 0)) (when (< i (vector-length v)) (process (vector-ref v i)) (loop (fx+ i 1))))"],
  ["(> i (vector-length v)) base case", "(let loop ((i 0)) (if (> i (vector-length v)) '() (begin (process (vector-ref v i)) (loop (+ i 1)))))"],
  ["hc-7 ascent to (vector-length v)", "(define (f v) (let loop ((i 0)) (if (>= i (vector-length v)) 0 (loop (+ i 1)))))"],
  ["hc-7 ascent with l passed in place", "(define (f lst) (let loop ((i 0) (l lst)) (if (>= i (length l)) 0 (loop (+ i 1) l))))"],
  ["hc-7 countdown under (<= k 0)", "(define (f n) (let loop ((k n)) (if (<= k 0) 0 (loop (- k 1)))))"],
  ["hc-7 countdown under when", "(define (f n) (let loop ((k n)) (when (> k 0) (loop (- k 1)))))"],
  ["hc-7 list walk with accumulator", "(define (f x) (let loop ((l x) (acc 0)) (if (null? l) acc (loop (cdr l) (+ acc 1)))))"],
  ["hc-7 nested loops, inner bound is the outer variable", "(define (f n) (let outer ((i 0)) (if (>= i n) 0 (let inner ((j 0)) (if (>= j i) (outer (+ i 1)) (inner (+ j 1)))))))"],
  ["hc-7 when (> 10 i)", "(define (f) (let loop ((i 0)) (when (> 10 i) (loop (+ i 1)))))"],
  ["hc-7 when (not (>= i 10))", "(define (f) (let loop ((i 0)) (when (not (>= i 10)) (loop (+ i 1)))))"],
  ["define-lambda body is walked", "(define g (lambda (n) (let loop ((k n)) (if (<= k 0) 0 (loop (- k 1))))))"],
  ["a quoted named let is data", "(display '(let loop ((n 1)) (loop n)))"],
  ["a dotted form is walked without raising", "(define (g . r) (let loop ((l r)) (if (null? l) 0 (loop (cdr l)))))"],
];

for (const [name, source] of accepted) {
  test(`accepted: ${name}`, () => assert.deepEqual(check(source), []));
}

const rejected: [name: string, source: string, kind: string][] = [
  ["no decreasing arg", "(let loop ((n 10)) (loop n))", "no-decreasing-arg"],
  ["base case but no decrease", "(let loop ((n 10)) (if (= n 0) 0 (loop n)))", "no-decreasing-arg"],
  ["decrease but no base case", "(let loop ((n 10)) (loop (- n 1)))", "no-base-case"],
  ["structural decrease but no base case", "(let loop ((lst '(1 2 3))) (display (car lst)) (loop (cdr lst)))", "no-base-case"],
  ["no args is infinite", "(let loop () (display \"forever\") (loop))", "no-decreasing-arg"],
  ["nested: inner invalid, outer valid", "(let outer ((i 10)) (if (= i 0) 0 (let inner ((j 5)) (inner j))))", "no-decreasing-arg"],
  ["opaque if test, non-recursive alternative", "(let loop ((n 10)) (if (some-check) (loop (- n 1)) 42))", "no-base-case"],
  ["when #t", "(let loop ((n 10)) (when #t (loop (- n 1))))", "no-base-case"],
  ["when with opaque test", "(let loop ((n 10)) (when (some-opaque-check) (loop (- n 1))))", "no-base-case"],
  ["unless #f", "(let loop ((n 10)) (unless #f (loop (- n 1))))", "no-base-case"],
  ["mixed decreasing and non-decreasing calls", "(let loop ((x 10)) (if (zero? x) 'done (begin (loop (- x 1)) (loop x))))", "no-decreasing-arg"],
  ["hc-6 named let under (= k 0)", "(define (f n) (let loop ((k n)) (if (= k 0) 0 (loop (- k 1)))))", "no-decreasing-arg"],
  ["hc-6 named let under (zero? n) with sub1", "(let loop ((n 10)) (if (zero? n) 0 (loop (sub1 n))))", "no-decreasing-arg"],
];

for (const [name, source, kind] of rejected) {
  test(`rejected: ${name}`, () => {
    const vs = check(source);
    assert.equal(vs.length, 1);
    assert.equal(vs[0]!.kind, kind);
  });
}

// assert-rejected cases: some violation, kind unchecked.
const flagged: [name: string, source: string][] = [
  ["hc-2 r3c2 closure re-enters with an earlier n", "(define (g) (let lp ((n 10) (k #f)) (cond ((= n 0) 0) (k (k k)) (else (lp (- n 1) (lambda (self) (lp (- n 1) self))))))) (g)"],
  ["hc-2 r3c3 loop variable named map", "(define (g) (let lp ((n 10) (k #f) (map (lambda (h l) h))) (cond ((= n 0) 0) (k (k k)) (else (lp (- n 1) (map (lambda (self) (lp (- n 1) self)) (list 1)) map))))) (g)"],
  ["hc-7 bound (length l) grows under (cons 1 l)", "(define (f lst) (let loop ((i 0) (l lst)) (if (>= i (length l)) 0 (loop (+ i 1) (cons 1 l)))))"],
  ["hc-7 test in an earlier statement guards nothing", "(define (f) (let loop ((i 0)) (if (>= i 10) 0 0) (loop (+ i 1))))"],
  ["hc-7 ascent with no upper-bound test", "(define (f n) (let loop ((i 0)) (if (= n 0) 0 (loop (+ i 1)))))"],
  ["hc-7 descent tested in another branch", "(define (f n) (let loop ((k n)) (if (<= k 0) (loop (- k 1)) 0)))"],
  ["hc-7 bound assigned by set!", "(define (f n) (let loop ((i 0)) (if (>= i n) 0 (begin (set! n (+ n 1)) (loop (+ i 1))))))"],
  ["hc-7 loop variable reset by set!", "(define (f l) (let loop ((x l)) (if (null? x) 0 (begin (set! x l) (loop (cdr x))))))"],
  ["hc-7 when (< i (length l)) with l grown", "(define (f lst) (let loop ((i 0) (l lst)) (when (< i (length l)) (loop (+ i 1) (cons 1 l)))))"],
  ["hc-7 when (> i 10) holds above the bound", "(define (f) (let loop ((i 0)) (when (> i 10) (loop (+ i 1)))))"],
  ["hc-7 when (< i 10) with descent", "(define (f) (let loop ((i 0)) (when (< i 10) (loop (- i 1)))))"],
  ["hc-7 when (< j 10) guards a different variable", "(define (f j) (let loop ((i 0)) (when (< j 10) (loop (+ i 1)))))"],
];

for (const [name, source] of flagged) {
  test(`flagged: ${name}`, () => assert.ok(check(source).length > 0));
}

test("a violation names the loop and carries the form by identity", () => {
  const [form] = readAll("(let loop ((n 10)) (loop n))");
  const [v] = analyzeNamedLetForms([form!]);
  assert.equal(v!.function!.name, "loop");
  assert.equal(v!.expr, form);
  assert.equal(v!.reason, 'named-let "loop" has no decreasing argument in recursive call(s)');
});

test("an equality stop gets the lower-stop hint", () => {
  const [v] = check("(let loop ((n 10)) (if (zero? n) 0 (loop (sub1 n))))");
  assert.match(v!.reason, /^named-let "loop" has no decreasing argument in recursive call\(s\)./);
  assert.notEqual(v!.reason, 'named-let "loop" has no decreasing argument in recursive call(s)');
});

test("violations come in walk order", () => {
  const vs = check("(let a ((n 1)) (a n)) (let b ((n 1)) (b (- n 1)))");
  assert.deepEqual(vs.map((v) => [v.function!.name, v.kind]), [["a", "no-decreasing-arg"], ["b", "no-base-case"]]);
});

const n = readOne("n");
const vars = [n];
test("baseCaseTest", () => {
  for (const t of ["(= n 0)", "(= 0 n)", "(zero? n)", "(< n 1)", "(<= n 0)", "(> 0 n)", "(>= 0 n)", "(>= n 9)", "(> n 9)", "(null? n)", "(not (pair? n))"]) {
    assert.ok(baseCaseTest(readOne(t), vars), t);
  }
  for (const t of ["(< 1 n)", "(<= 0 n)", "(= n n)", "(pair? n)", "(null? m)", "(zero?)", "n"]) {
    assert.ok(!baseCaseTest(readOne(t), vars), t);
  }
});

test("negatedBaseCaseTest", () => {
  for (const t of ["(pair? n)", "(not (zero? n))", "(> n 0)", "(positive? n)"]) assert.ok(negatedBaseCaseTest(readOne(t), vars), t);
  for (const t of ["(pair? n m)", "(not (pair? n))", "(> n n)", "(foo n)"]) assert.ok(!negatedBaseCaseTest(readOne(t), vars), t);
});

test("condFallThroughTest", () => {
  assert.equal(condFallThroughTest(readOne("(cond ((> n 0) 1) (else 2))")), null);
  assert.equal(condFallThroughTest(readOne("(cond)")), null);
  assert.deepEqual(condFallThroughTest(readOne("(cond ((= n 1) 1) ((> n 0) 2))")), readOne("(> n 0)"));
});

test("hasBaseCase: a cond without else falls through (HC-8)", () => {
  const loop = readOne("loop");
  assert.ok(hasBaseCase(readAll("(cond ((> n 0) (loop (- n 1))))"), loop, vars));
  assert.ok(!hasBaseCase(readAll("(cond ((foo) (loop (- n 1))))"), loop, vars));
});
