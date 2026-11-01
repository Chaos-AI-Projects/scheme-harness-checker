// The mutual-recursion pass of termination.ss (HC-17, Phase 6). Cases are the "Mutual recursion
// analysis" groups of test-termination.ss (from line 851). Each program there has no other loop
// that fails, so this pass alone decides its verdict.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, readOne, sym } from "../src/sexp.ts";
import { buildCallGraph } from "../src/termination/callgraph.ts";
import { acyclic, analyzeMutualRecursion, containsSccCall, sccHasBaseCase } from "../src/termination/mutualrec.ts";

const check = (source: string) => analyzeMutualRecursion(readAll(source));

const accepted: [name: string, source: string][] = [
  [
    "even?/odd? with decrease and base case",
    "(define (my-even? n) (if (<= n 0) #t (my-odd? (- n 1)))) (define (my-odd? n) (if (<= n 0) #f (my-even? (- n 1))))",
  ],
  [
    "three-function cycle with decrease",
    "(define (a n) (if (<= n 0) 'done (b (- n 1)))) (define (b n) (if (<= n 0) 'done (c (- n 1)))) (define (c n) (if (<= n 0) 'done (a (- n 1))))",
  ],
  [
    "both functions decrease before calling partner",
    "(define (ping n) (if (<= n 0) 'done (pong (- n 1)))) (define (pong n) (if (<= n 0) 'done (ping (- n 1))))",
  ],
  [
    "letrec-bound even/odd",
    "(letrec ((ev (lambda (n) (if (<= n 0) #t (od (- n 1))))) (od (lambda (n) (if (<= n 0) #f (ev (- n 1)))))) (ev 10))",
  ],
  [
    "structural decrease with cdr",
    "(define (process-a lst) (if (null? lst) '() (process-b (cdr lst)))) (define (process-b lst) (if (null? lst) '() (process-a (cdr lst))))",
  ],
  ["direct recursion is left to Phase 5", "(define (f n) (f n))"],
];

for (const [name, source] of accepted) {
  test(`mutual recursion accepts: ${name}`, () => assert.deepEqual(check(source), []));
}

const rejected: [name: string, source: string, kind: string][] = [
  ["no decrease flags both", "(define (ping n) (pong n)) (define (pong n) (ping n))", "no-decreasing-arg"],
  ["decrease but no base case flags both", "(define (down-a n) (down-b (- n 1))) (define (down-b n) (down-a (- n 1)))", "no-base-case"],
  ["no edge decreases flags both", "(define (alpha n) (if (= n 0) 'done (beta n))) (define (beta n) (alpha n))", "no-decreasing-arg"],
  [
    "self-loop without decrease in SCC",
    "(define (loop-a n) (loop-a n) (loop-b (- n 1))) (define (loop-b n) (if (= n 0) 'done (loop-a (- n 1))))",
    "no-decreasing-arg",
  ],
  ["a member without formals fails closed", "(define (a) (b 1)) (define (b n) (if (<= n 0) 0 (a)))", "no-decreasing-arg"],
];

for (const [name, source, kind] of rejected) {
  test(`mutual recursion rejects: ${name}`, () => {
    const violations = check(source);
    assert.equal(violations.length, 2);
    for (const v of violations) assert.equal(v.kind, kind);
  });
}

test("one violation per member, each carrying its own defining form", () => {
  const exprs = readAll("(define (pong n) (ping n)) (define (ping n) (pong n))");
  const violations = analyzeMutualRecursion(exprs);
  assert.deepEqual(violations.map((v) => v.function), [sym("pong"), sym("ping")]);
  assert.equal(violations[0]!.expr, exprs[0]);
  assert.equal(violations[1]!.expr, exprs[1]);
});

test("reasons name the group sorted, as the Scheme's text does", () => {
  const [v] = check("(define (pong n) (ping n)) (define (ping n) (pong n))");
  assert.equal(v!.reason, "mutual recursion group (ping, pong) has no decreasing argument across call edges");
  const [w] = check("(define (down-b n) (down-a (- n 1))) (define (down-a n) (down-b (- n 1)))");
  assert.equal(w!.reason, "mutual recursion group (down-a, down-b) has no reachable base case");
});

test("containsSccCall walks by car and cdr, as the Scheme does", () => {
  const members = [sym("f")];
  assert.equal(containsSccCall(readOne("(g (f 1))"), members), true);
  // A member's name anywhere in a list is found, not only in operator position.
  assert.equal(containsSccCall(readOne("(map f xs)"), members), true);
  assert.equal(containsSccCall(readOne("'(f 1)"), members), false);
  // A tail that reads (quote ...) hides the rest of the list.
  assert.equal(containsSccCall(readOne("(list quote (f 1))"), members), false);
  assert.equal(containsSccCall(readOne("(g . f)"), members), false);
  assert.equal(containsSccCall(sym("f"), members), false);
});

test("acyclic", () => {
  const succ = (edges: Record<string, string[]>) => (n: string) => edges[n] ?? [];
  assert.equal(acyclic(["a", "b"], succ({ a: ["b"] })), true);
  assert.equal(acyclic(["a", "b"], succ({ a: ["b"], b: ["a"] })), false);
  assert.equal(acyclic(["a"], succ({ a: ["a"] })), false);
  assert.equal(acyclic([], succ({})), true);
});

test("sccHasBaseCase: a cycle avoiding every based member fails", () => {
  // a has a base case, but b and c call each other without one.
  const src =
    "(define (a n) (if (<= n 0) 0 (b (- n 1)))) (define (b n) (c (- n 1)) (a n)) (define (c n) (b (- n 1)))";
  const exprs = readAll(src);
  const graph = buildCallGraph(exprs);
  assert.equal(sccHasBaseCase(exprs, [sym("a"), sym("b"), sym("c")], graph), false);
  const ok = readAll("(define (a n) (if (<= n 0) 0 (b (- n 1)))) (define (b n) (a (- n 1)))");
  assert.equal(sccHasBaseCase(ok, [sym("a"), sym("b")], buildCallGraph(ok)), true);
});

test("sccHasBaseCase: an if test that calls a member is no base case", () => {
  const exprs = readAll("(define (a n) (if (= n (b 1)) 0 (b (- n 1)))) (define (b n) (a (- n 1)))");
  assert.equal(sccHasBaseCase(exprs, [sym("a"), sym("b")], buildCallGraph(exprs)), false);
});
