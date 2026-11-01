// The do-loop pass of termination.ss (HC-16, Phase 3). Cases are the do-form groups of
// test-termination.ss: "Do-form analysis" (from line 440), HC-5 (2390), HC-6 (2519) and HC-10
// (2648). Each program there is do-loops only, so this pass alone decides its verdict.

import { test } from "node:test";
import assert from "node:assert/strict";
import { readAll, readOne, write } from "../src/sexp.ts";
import { analyzeDoForms, doContinueGuards, doStepsProgress } from "../src/termination/do.ts";

const check = (source: string) => analyzeDoForms(readAll(source));

const accepted: [name: string, source: string][] = [
  ["do with step and test passes", "(do ((i 0 (+ i 1))) ((= i 10)) (display i))"],
  ["do with multiple bindings, one has step", "(do ((i 0 (+ i 1)) (j 0)) ((= i 10)) (display i))"],
  ["do with all bindings having steps", "(do ((i 0 (+ i 1)) (j 10 (- j 1))) ((= i 10)) (display j))"],
  ["do nested inside define passes when valid", "(define (count-up n) (do ((i 0 (+ i 1))) ((= i n)) (display i)))"],
  ["nested valid do-forms", "(do ((i 0 (+ i 1))) ((= i 5)) (do ((j 0 (+ j 1))) ((= j 3)) (display j)))"],
  ["do-form with increasing vector index", "(do ((i 0 (+ i 1))) ((= i (vector-length v)) result) (process (vector-ref v i)))"],
  ["do-form with increasing index and >= test", "(do ((i 0 (+ i 1))) ((>= i (vector-length v))) (process (vector-ref v i)))"],
  ["hc-5 count up to a literal", "(do ((i 0 (+ i 1))) ((>= i 3) 0))"],
  ["hc-5 mirrored upper bound", "(do ((i 0 (+ i 1))) ((<= 3 i) 0))"],
  ["hc-5 countdown to (<= n 0)", "(do ((n 10 (- n 1))) ((<= n 0) 0))"],
  ["hc-5 countdown under a negated pass test", "(do ((n 10 (sub1 n))) ((not (> n 0)) 0))"],
  ["hc-5 mirrored lower bound", "(do ((n 10 (- n 1))) ((>= 0 n) 0))"],
  ["hc-5 list walk", "(do ((l '(1 2 3) (cdr l)) (s 0 (+ s (car l)))) ((null? l) s))"],
  ["hc-5 disjunction with one progressing test", "(do ((i 0 (+ i 1)) (l '(1 2) (cdr l))) ((or (eq? l 'x) (>= i 10)) i))"],
  ["hc-5 vector-length bound", "(define (g v) (do ((i 0 (+ i 1))) ((>= i (vector-length v)) 0))) (g (vector 1 2))"],
  ["hc-5 unstepped loop variable as bound", "(do ((i 0 (+ i 1)) (n 5)) ((>= i n) i))"],
  ["hc-5 set! of an unrelated variable", "(define (g) (let ((acc 0)) (do ((i 0 (+ i 1))) ((>= i 3) acc) (set! acc (+ acc i))))) (g)"],
  ["hc-10 do-loop stepping by (list-tail l 1)", "(do ((l '(1 2) (list-tail l 1))) ((null? l) 0))"],
  ["a quoted do-form is data", "(display '(do ((i 0)) (#f)))"],
  ["a dotted form is walked without raising", "(define (g . r) (do ((i 0 (+ i 1))) ((>= i 3) r)))"],
];

for (const [name, source] of accepted) {
  test(`accepted: ${name}`, () => assert.deepEqual(check(source), []));
}

const rejected: [name: string, source: string, reason: string][] = [
  ["do with #f test", "(do ((i 0 (+ i 1))) (#f) (display i))", "do-form has unreachable exit condition"],
  ["do without step", "(do ((i 0)) ((= i 10)) (display i))", "do-form has no step expressions; loop variables never change"],
  ["do test not referencing loop var", "(do ((i 0 (+ i 1))) ((= x 10)) (display i))", "do-form exit test does not reference any loop variable"],
  ["hc-5 step leaves the tested variable unchanged", "(define (g) (do ((i 0 i)) ((>= i 3) 0))) (display (g))", "PROGRESS"],
  ["hc-5 descent under an upper-bound exit test", "(do ((i 0 (- i 1))) ((>= i 3) 0))", "PROGRESS"],
  ["hc-5 ascent under a lower-bound exit test", "(do ((i 0 (+ i 1))) ((<= i -1) 0))", "PROGRESS"],
  ["hc-5 stepped variable is not the tested one", "(do ((i 0 (+ i 1)) (j 0 j)) ((>= j 3) 0))", "PROGRESS"],
  ["hc-5 bound is a stepped loop variable", "(do ((i 0 (+ i 1)) (n 3 (+ n 1))) ((>= i n) 0))", "PROGRESS"],
  ["hc-5 two stepped variables that can cross", "(do ((i 0 (+ i 1)) (j 11 (- j 1))) ((= i j) 0))", "PROGRESS"],
  ["hc-5 body resets the progress variable", "(do ((i 0 (+ i 1))) ((>= i 3) 0) (set! i 0))", "PROGRESS"],
  ["hc-5 bound assigned in the body", "(define n 3) (define (g) (do ((i 0 (+ i 1))) ((>= i n) 0) (set! n (+ n 1)))) (g)", "PROGRESS"],
  ["hc-5 bound is a user call", "(define (f) 3) (do ((i 0 (+ i 1))) ((>= i (f)) 0))", "PROGRESS"],
  ["hc-5 do-loop with no variables", "(define (g) (do () ((= 1 2) 0))) (g)", "PROGRESS"],
  ["hc-5 conjunction gives no stop", "(do ((i 0 (+ i 1))) ((and (>= i 3) (< i 0)) 0))", "PROGRESS"],
  ["hc-6 do-loop countdown to (zero? n)", "(do ((n 10 (- n 1))) ((zero? n) 0))", "PROGRESS"],
  ["hc-6 do-loop countdown to (= n 0)", "(do ((n 10 (- n 1))) ((= n 0) 0))", "PROGRESS"],
  ["hc-10 do-loop stepping by (list-tail l 0)", "(do ((l '(1 2) (list-tail l 0))) ((null? l) 0))", "PROGRESS"],
];

const PROGRESS = "do-form has no step that moves a tested variable toward the exit test";

for (const [name, source, reason] of rejected) {
  test(`rejected: ${name}`, () => {
    const vs = check(source);
    assert.equal(vs.length, 1);
    assert.equal(vs[0]!.kind, "infinite-loop");
    assert.equal(vs[0]!.function, null);
    assert.ok(vs[0]!.reason.startsWith(reason === "PROGRESS" ? PROGRESS : reason), vs[0]!.reason);
  });
}

test("the violation carries the do-form itself", () => {
  const exprs = readAll("(define (f) (do ((i 0)) ((= i 10)) i))");
  const vs = analyzeDoForms(exprs);
  assert.equal(vs[0]!.expr, (exprs[0] as unknown[])[2]);
});

test("nested do: only the inner invalid one is flagged", () => {
  const vs = check("(do ((i 0 (+ i 1))) ((= i 5)) (do ((j 0)) ((= j 3)) (display j)))");
  assert.equal(vs.length, 1);
  assert.equal(write(vs[0]!.expr), "(do ((j 0)) ((= j 3)) (display j))");
});

test("violations come in source order", () => {
  const vs = check("(do ((i 0)) ((= i 1))) (do ((k 0 (+ k 1))) (#f))");
  assert.deepEqual(vs.map((v) => v.reason.slice(0, 20)), ["do-form has no step ", "do-form has unreacha"]);
});

test("hc-6 do-loop reason names (<= n 0)", () => {
  assert.ok(check("(do ((n 10 (- n 1))) ((zero? n) 0))")[0]!.reason.includes("(<= n 0)"));
});

test("hc-6 do-loop ascent to (= i 0) gets no hint", () => {
  const vs = check("(do ((i -5 (+ i 1))) ((= i 0) 0))");
  assert.equal(vs.length, 1);
  assert.ok(!vs[0]!.reason.includes("(<="));
});

test("doContinueGuards: or splits, < and <= gain their flipped form", () => {
  const show = (t: string) => doContinueGuards(readOne(t)).map(([g, k]) => `${write(g)}:${k}`);
  assert.deepEqual(show("(>= i 3)"), ["(>= i 3):false"]);
  assert.deepEqual(show("(<= 3 i)"), ["(<= 3 i):false", "(>= i 3):false"]);
  assert.deepEqual(show("(< 3 i)"), ["(< 3 i):false", "(> i 3):false"]);
  assert.deepEqual(show("(or (null? l) (< 3 i))"), ["(null? l):false", "(< 3 i):false", "(> i 3):false"]);
});

test("doStepsProgress: ascent under a stable upper bound", () => {
  assert.equal(doStepsProgress(readOne("(do ((i 0 (+ i 1))) ((>= i 3)))"), []), true);
  assert.equal(doStepsProgress(readOne("(do ((i 0 (+ i 1))) ((>= i n)))"), [readOne("n")]), false);
});
